# bolt_manager_schema_aware.py

import sys
import os
import atexit
import pyodbc
import json
import csv
import time
from pathlib import Path
from datetime import datetime
from functools import wraps
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Any
from PyQt5.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QLabel, QPushButton, QComboBox,
    QListWidget, QTableWidget, QTableWidgetItem, QHBoxLayout, QLineEdit, 
    QCheckBox, QMessageBox, QProgressBar, QHeaderView, QMenu, QAction,
    QScrollArea, QDialog, QListWidgetItem, QWidgetAction, QToolBar,
    QStatusBar, QFileDialog, QShortcut, QGroupBox, QSpinBox, QDoubleSpinBox,
    QTextEdit, QTabWidget, QFormLayout, QDialogButtonBox
)
from PyQt5.QtCore import Qt, QThread, pyqtSignal, QTimer
from PyQt5.QtGui import QKeySequence, QColor, QFont

# Configuration class for better path management
class Config:
    @staticmethod
    def get_db_path():
        """Get database path with fallback options"""
        # Allow environment variable override
        custom_path = os.environ.get('ADVSTEEL_DB_PATH')
        if custom_path and Path(custom_path).exists():
            return custom_path
        
        # Default path with year flexibility
        base_path = Path(r'C:\PROGRAMDATA\AUTODESK\ADVANCE STEEL')
        for year in range(2025, 2020, -1):  # Check recent years
            db_path = base_path / str(year) / 'USA/STEEL/DATA/ASTORBASE.MDF'
            if db_path.exists():
                return str(db_path)
        
        # Fallback to hardcoded path
        return r'C:\PROGRAMDATA\AUTODESK\ADVANCE STEEL 2025\USA\STEEL\DATA\ASTORBASE.MDF'

DB_CONFIG = {
    'server': r'(LocalDB)\ADVANCESTEEL2025',
    'trusted_connection': 'yes',
    'driver': 'ODBC Driver 17 for SQL Server',
    'database': Config.get_db_path()
}

# Configuration for unit conversion
UNIT_CONVERT = {
    'Diameter': True, 
    'Length': True, 
    'HeadHeight': True,
    'Width': True,
    'Height': True,
    'Thickness': True,
    'HeadDiameter': True,
    'NutThickness': True,
    'WasherThickness': True,
    'WasherOuterDia': True,
    'GripMin': True,
    'GripMax': True
}
MM_TO_INCH = 25.4

# Known fastener tables with their relationships
FASTENER_TABLES = {
    'BoltsCoating', 'BoltsDiameters', 'Screw', 'SetBolts', 'SetBoltsType', 'SetOfBolts', 'Standard',
    'BoltsDistances', 'BoltDefinition', 'TappingHole', 'Sources', 'Sets', 'SetNutsBolts', 'ScrewNew',
    'Authors', 'StrengthClass', 'AutoLength', 'StandardNuts'
}

# Critical table relationships for bolt creation
BOLT_SCHEMA = {
    'BoltDefinition': {
        'foreign_keys': {
            'StandardId': 'Standard',
            'StrengthClassId': 'StrengthClass',
            'AuthorId': 'Authors'
        },
        'required_fields': ['Name', 'StandardId', 'Diameter', 'StrengthClassId', 'AuthorId'],
        'description': 'Base bolt type definitions'
    },
    'SetBolts': {
        'foreign_keys': {
            'BoltDefId': 'BoltDefinition'
        },
        'required_fields': ['BoltDefId', 'Length', 'Weight', 'PartName'],
        'description': 'Individual bolt lengths'
    },
    'SetOfBolts': {
        'foreign_keys': {
            'BoltDefId': 'BoltDefinition',
            'SetId': 'Sets'
        },
        'required_fields': ['BoltDefId', 'SetId'],
        'description': 'Links bolts to assembly sets'
    },
    'SetNutsBolts': {
        'foreign_keys': {
            'StandardId': 'Standard',
            'SetId': 'Sets'
        },
        'required_fields': ['StandardId', 'SetId', 'Diameter', 'NutThickness', 'WasherThickness'],
        'description': 'Nut and washer dimensions'
    },
    'AutoLength': {
        'foreign_keys': {
            'BoltDefId': 'BoltDefinition'
        },
        'required_fields': ['BoltDefId', 'GripMin', 'GripMax', 'Length'],
        'description': 'Automatic length selection rules'
    }
}

@dataclass
class BoltData:
    """Data class for bolt information"""
    name: str
    standard_id: int
    diameter: float
    strength_class_id: int
    author_id: int
    head_diameter: float = None
    head_height: float = None
    thread_type: str = 'metric_coarse'
    lengths: List[Tuple[float, float, str]] = None  # (length, weight, part_name)
    assembly_sets: List[int] = None  # Set IDs
    
class DatabaseTransaction:
    """Context manager for database transactions"""
    def __init__(self, connection):
        self.connection = connection
        self.cursor = None
        
    def __enter__(self):
        self.cursor = self.connection.cursor()
        self.connection.commit()  # Ensure clean state
        return self.cursor
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self.connection.commit()
        else:
            self.connection.rollback()
            print(f"Transaction rolled back due to: {exc_val}")
        if self.cursor:
            self.cursor.close()

class BoltCreationWizard(QDialog):
    """Wizard for creating new bolts with proper schema compliance"""
    
    def __init__(self, cursor, parent=None):
        super().__init__(parent)
        self.cursor = cursor
        self.bolt_data = None
        self.setWindowTitle("Create New Bolt Assembly")
        self.resize(800, 600)
        self.init_ui()
        self.load_reference_data()
        
    def init_ui(self):
        layout = QVBoxLayout()
        
        # Tab widget for steps
        self.tabs = QTabWidget()
        
        # Step 1: Basic Properties
        self.basic_tab = self.create_basic_tab()
        self.tabs.addTab(self.basic_tab, "1. Basic Properties")
        
        # Step 2: Lengths
        self.lengths_tab = self.create_lengths_tab()
        self.tabs.addTab(self.lengths_tab, "2. Bolt Lengths")
        
        # Step 3: Assembly Sets
        self.assembly_tab = self.create_assembly_tab()
        self.tabs.addTab(self.assembly_tab, "3. Assembly Sets")
        
        # Step 4: Nut/Washer Data
        self.nut_washer_tab = self.create_nut_washer_tab()
        self.tabs.addTab(self.nut_washer_tab, "4. Nut/Washer Data")
        
        # Step 5: Auto Length Rules
        self.auto_length_tab = self.create_auto_length_tab()
        self.tabs.addTab(self.auto_length_tab, "5. Auto Length (Optional)")
        
        # Step 6: Preview
        self.preview_tab = self.create_preview_tab()
        self.tabs.addTab(self.preview_tab, "6. Preview & Create")
        
        layout.addWidget(self.tabs)
        
        # Buttons
        button_box = QDialogButtonBox(
            QDialogButtonBox.Ok | QDialogButtonBox.Cancel
        )
        button_box.accepted.connect(self.create_bolt)
        button_box.rejected.connect(self.reject)
        
        layout.addWidget(button_box)
        self.setLayout(layout)
        
    def create_basic_tab(self):
        """Create tab for basic bolt properties"""
        widget = QWidget()
        layout = QFormLayout()
        
        # Name
        self.name_input = QLineEdit()
        self.name_input.setPlaceholderText("e.g., Bolt M16-70 DIN 6914")
        layout.addRow("Bolt Name:", self.name_input)
        
        # Standard
        self.standard_combo = QComboBox()
        layout.addRow("Standard:", self.standard_combo)
        
        # Diameter
        self.diameter_input = QDoubleSpinBox()
        self.diameter_input.setRange(1.0, 100.0)
        self.diameter_input.setSuffix(" mm")
        self.diameter_input.setValue(16.0)
        layout.addRow("Diameter:", self.diameter_input)
        
        # Strength Class
        self.strength_combo = QComboBox()
        layout.addRow("Strength Class:", self.strength_combo)
        
        # Author
        self.author_combo = QComboBox()
        layout.addRow("Author:", self.author_combo)
        
        # Head dimensions
        group = QGroupBox("Head Dimensions")
        head_layout = QFormLayout()
        
        self.head_diameter_input = QDoubleSpinBox()
        self.head_diameter_input.setRange(1.0, 200.0)
        self.head_diameter_input.setSuffix(" mm")
        self.head_diameter_input.setValue(24.0)
        head_layout.addRow("Head Diameter/Width:", self.head_diameter_input)
        
        self.head_height_input = QDoubleSpinBox()
        self.head_height_input.setRange(1.0, 100.0)
        self.head_height_input.setSuffix(" mm")
        self.head_height_input.setValue(10.0)
        head_layout.addRow("Head Height:", self.head_height_input)
        
        group.setLayout(head_layout)
        layout.addRow(group)
        
        widget.setLayout(layout)
        return widget
        
    def create_lengths_tab(self):
        """Create tab for bolt lengths"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        # Instructions
        layout.addWidget(QLabel("Add bolt lengths:"))
        
        # Length input
        input_layout = QHBoxLayout()
        
        self.length_input = QDoubleSpinBox()
        self.length_input.setRange(10.0, 1000.0)
        self.length_input.setSuffix(" mm")
        self.length_input.setValue(70.0)
        input_layout.addWidget(QLabel("Length:"))
        input_layout.addWidget(self.length_input)
        
        self.weight_input = QDoubleSpinBox()
        self.weight_input.setRange(0.001, 10.0)
        self.weight_input.setSuffix(" kg")
        self.weight_input.setDecimals(3)
        self.weight_input.setValue(0.138)
        input_layout.addWidget(QLabel("Weight:"))
        input_layout.addWidget(self.weight_input)
        
        add_btn = QPushButton("Add Length")
        add_btn.clicked.connect(self.add_length)
        input_layout.addWidget(add_btn)
        
        layout.addLayout(input_layout)
        
        # Length list
        self.lengths_table = QTableWidget()
        self.lengths_table.setColumnCount(3)
        self.lengths_table.setHorizontalHeaderLabels(["Length (mm)", "Weight (kg)", "Part Name"])
        layout.addWidget(self.lengths_table)
        
        # Bulk add button
        bulk_btn = QPushButton("Bulk Add Standard Lengths...")
        bulk_btn.clicked.connect(self.bulk_add_lengths)
        layout.addWidget(bulk_btn)
        
        widget.setLayout(layout)
        return widget
        
    def create_assembly_tab(self):
        """Create tab for assembly sets"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        layout.addWidget(QLabel("Select allowed assembly sets:"))
        
        # Assembly set list
        self.assembly_list = QListWidget()
        self.assembly_list.setSelectionMode(QListWidget.MultiSelection)
        layout.addWidget(self.assembly_list)
        
        widget.setLayout(layout)
        return widget
        
    def create_nut_washer_tab(self):
        """Create tab for nut/washer data"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        layout.addWidget(QLabel("Verify nut and washer dimensions:"))
        
        # Input for current diameter
        check_layout = QHBoxLayout()
        check_btn = QPushButton("Check Existing Data")
        check_btn.clicked.connect(self.check_nut_washer_data)
        check_layout.addWidget(check_btn)
        layout.addLayout(check_layout)
        
        # Data display
        self.nut_washer_text = QTextEdit()
        self.nut_washer_text.setReadOnly(True)
        layout.addWidget(self.nut_washer_text)
        
        # Manual entry section
        group = QGroupBox("Add Missing Data")
        form_layout = QFormLayout()
        
        self.nut_thickness_input = QDoubleSpinBox()
        self.nut_thickness_input.setRange(1.0, 100.0)
        self.nut_thickness_input.setSuffix(" mm")
        form_layout.addRow("Nut Thickness:", self.nut_thickness_input)
        
        self.nut_width_input = QDoubleSpinBox()
        self.nut_width_input.setRange(1.0, 200.0)
        self.nut_width_input.setSuffix(" mm")
        form_layout.addRow("Nut Width AF:", self.nut_width_input)
        
        self.washer_thickness_input = QDoubleSpinBox()
        self.washer_thickness_input.setRange(0.5, 20.0)
        self.washer_thickness_input.setSuffix(" mm")
        form_layout.addRow("Washer Thickness:", self.washer_thickness_input)
        
        self.washer_diameter_input = QDoubleSpinBox()
        self.washer_diameter_input.setRange(1.0, 200.0)
        self.washer_diameter_input.setSuffix(" mm")
        form_layout.addRow("Washer Outer Dia:", self.washer_diameter_input)
        
        group.setLayout(form_layout)
        layout.addWidget(group)
        
        widget.setLayout(layout)
        return widget
        
    def create_auto_length_tab(self):
        """Create tab for auto length rules"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        layout.addWidget(QLabel("Optional: Define automatic length selection rules"))
        
        # Enable checkbox
        self.enable_auto_length = QCheckBox("Enable automatic length selection")
        layout.addWidget(self.enable_auto_length)
        
        # Auto-generate button
        generate_btn = QPushButton("Generate Standard Rules")
        generate_btn.clicked.connect(self.generate_auto_length_rules)
        layout.addWidget(generate_btn)
        
        # Rules table
        self.auto_length_table = QTableWidget()
        self.auto_length_table.setColumnCount(3)
        self.auto_length_table.setHorizontalHeaderLabels(["Grip Min", "Grip Max", "Length"])
        layout.addWidget(self.auto_length_table)
        
        widget.setLayout(layout)
        return widget
        
    def create_preview_tab(self):
        """Create preview tab"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        layout.addWidget(QLabel("Review bolt data before creation:"))
        
        # Preview button
        preview_btn = QPushButton("Generate Preview")
        preview_btn.clicked.connect(self.generate_preview)
        layout.addWidget(preview_btn)
        
        # Preview text
        self.preview_text = QTextEdit()
        self.preview_text.setReadOnly(True)
        layout.addWidget(self.preview_text)
        
        # SQL preview
        self.sql_preview = QTextEdit()
        self.sql_preview.setReadOnly(True)
        self.sql_preview.setMaximumHeight(200)
        layout.addWidget(QLabel("SQL Commands to be executed:"))
        layout.addWidget(self.sql_preview)
        
        widget.setLayout(layout)
        return widget
        
    def load_reference_data(self):
        """Load reference data for dropdowns"""
        try:
            # Load standards
            self.cursor.execute("SELECT ID, Name FROM Standard ORDER BY Name")
            standards = self.cursor.fetchall()
            for std_id, name in standards:
                self.standard_combo.addItem(name, std_id)
            
            # Load strength classes
            self.cursor.execute("SELECT ID, Name FROM StrengthClass ORDER BY Name")
            strengths = self.cursor.fetchall()
            for str_id, name in strengths:
                self.strength_combo.addItem(name, str_id)
            
            # Load authors
            self.cursor.execute("SELECT ID, Name FROM Authors ORDER BY Name")
            authors = self.cursor.fetchall()
            for auth_id, name in authors:
                self.author_combo.addItem(name, auth_id)
            
            # Load assembly sets
            self.cursor.execute("SELECT ID, SetCode, Description FROM Sets ORDER BY SetCode")
            sets = self.cursor.fetchall()
            for set_id, code, desc in sets:
                item_text = f"{code} - {desc}" if desc else code
                item = QListWidgetItem(item_text)
                item.setData(Qt.UserRole, set_id)
                self.assembly_list.addItem(item)
            
        except Exception as e:
            QMessageBox.warning(self, "Load Error", f"Error loading reference data: {str(e)}")
            
    def add_length(self):
        """Add a bolt length to the table"""
        length = self.length_input.value()
        weight = self.weight_input.value()
        diameter = self.diameter_input.value()
        part_name = f"M{int(diameter)}x{int(length)}"
        
        row = self.lengths_table.rowCount()
        self.lengths_table.insertRow(row)
        self.lengths_table.setItem(row, 0, QTableWidgetItem(str(length)))
        self.lengths_table.setItem(row, 1, QTableWidgetItem(str(weight)))
        self.lengths_table.setItem(row, 2, QTableWidgetItem(part_name))
        
    def bulk_add_lengths(self):
        """Bulk add standard lengths"""
        dialog = QDialog(self)
        dialog.setWindowTitle("Bulk Add Lengths")
        layout = QVBoxLayout()
        
        # Range inputs
        form_layout = QFormLayout()
        
        start_input = QSpinBox()
        start_input.setRange(10, 1000)
        start_input.setValue(30)
        form_layout.addRow("Start Length (mm):", start_input)
        
        end_input = QSpinBox()
        end_input.setRange(10, 1000)
        end_input.setValue(200)
        form_layout.addRow("End Length (mm):", end_input)
        
        increment_input = QSpinBox()
        increment_input.setRange(5, 50)
        increment_input.setValue(10)
        form_layout.addRow("Increment (mm):", increment_input)
        
        layout.addLayout(form_layout)
        
        # Buttons
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        layout.addWidget(buttons)
        
        dialog.setLayout(layout)
        
        if dialog.exec_():
            # Generate lengths
            diameter = self.diameter_input.value()
            for length in range(start_input.value(), end_input.value() + 1, increment_input.value()):
                # Estimate weight (simplified formula)
                weight = round(length * diameter * diameter * 0.00000617, 3)
                part_name = f"M{int(diameter)}x{int(length)}"
                
                row = self.lengths_table.rowCount()
                self.lengths_table.insertRow(row)
                self.lengths_table.setItem(row, 0, QTableWidgetItem(str(length)))
                self.lengths_table.setItem(row, 1, QTableWidgetItem(str(weight)))
                self.lengths_table.setItem(row, 2, QTableWidgetItem(part_name))
                
    def check_nut_washer_data(self):
        """Check existing nut/washer data"""
        standard_id = self.standard_combo.currentData()
        diameter = self.diameter_input.value()
        
        # Get selected assembly sets
        selected_sets = []
        for i in range(self.assembly_list.count()):
            item = self.assembly_list.item(i)
            if item.isSelected():
                selected_sets.append((item.data(Qt.UserRole), item.text()))
        
        if not selected_sets:
            self.nut_washer_text.setText("Please select at least one assembly set first.")
            return
            
        report = []
        missing = []
        
        for set_id, set_name in selected_sets:
            query = """
                SELECT NutThickness, NutWidthAcrossFlats, WasherThickness, WasherOuterDia
                FROM SetNutsBolts
                WHERE StandardId = ? AND SetId = ? AND Diameter = ?
            """
            self.cursor.execute(query, (standard_id, set_id, diameter))
            result = self.cursor.fetchone()
            
            if result:
                report.append(f"✓ {set_name}:")
                report.append(f"  Nut: {result[0]}mm thick, {result[1]}mm AF")
                report.append(f"  Washer: {result[2]}mm thick, {result[3]}mm OD")
            else:
                report.append(f"✗ {set_name}: NO DATA FOUND")
                missing.append(set_id)
                
        self.nut_washer_text.setText("\n".join(report))
        
        if missing:
            QMessageBox.warning(self, "Missing Data", 
                              f"Missing nut/washer data for {len(missing)} assembly set(s). "
                              "Please add the data below.")
                              
    def generate_auto_length_rules(self):
        """Generate standard auto-length rules"""
        if self.lengths_table.rowCount() == 0:
            QMessageBox.warning(self, "No Lengths", "Please add bolt lengths first.")
            return
            
        # Get all lengths
        lengths = []
        for row in range(self.lengths_table.rowCount()):
            length = float(self.lengths_table.item(row, 0).text())
            lengths.append(length)
        lengths.sort()
        
        # Clear existing rules
        self.auto_length_table.setRowCount(0)
        
        # Generate rules (simplified algorithm)
        # Typically: bolt_length = grip + nut_height + 2-3 threads projection
        nut_height = self.nut_thickness_input.value() or 13.0  # Default for M16
        thread_projection = 3.0  # 3mm projection
        
        for length in lengths:
            max_grip = length - nut_height - thread_projection
            min_grip = 0 if self.auto_length_table.rowCount() == 0 else prev_max_grip + 0.1
            
            if max_grip > min_grip:
                row = self.auto_length_table.rowCount()
                self.auto_length_table.insertRow(row)
                self.auto_length_table.setItem(row, 0, QTableWidgetItem(f"{min_grip:.1f}"))
                self.auto_length_table.setItem(row, 1, QTableWidgetItem(f"{max_grip:.1f}"))
                self.auto_length_table.setItem(row, 2, QTableWidgetItem(str(length)))
                
                prev_max_grip = max_grip
                
    def generate_preview(self):
        """Generate preview of bolt data"""
        # Collect all data
        bolt_name = self.name_input.text()
        if not bolt_name:
            QMessageBox.warning(self, "Incomplete Data", "Please enter a bolt name.")
            return
            
        preview_lines = [
            "=== BOLT CREATION PREVIEW ===",
            f"Name: {bolt_name}",
            f"Standard: {self.standard_combo.currentText()}",
            f"Diameter: {self.diameter_input.value()} mm",
            f"Strength Class: {self.strength_combo.currentText()}",
            f"Author: {self.author_combo.currentText()}",
            f"Head Dimensions: {self.head_diameter_input.value()}mm x {self.head_height_input.value()}mm",
            "",
            f"Lengths: {self.lengths_table.rowCount()} entries",
        ]
        
        # Selected assembly sets
        selected_count = len([i for i in range(self.assembly_list.count()) 
                            if self.assembly_list.item(i).isSelected()])
        preview_lines.append(f"Assembly Sets: {selected_count} selected")
        
        # Auto length
        if self.enable_auto_length.isChecked():
            preview_lines.append(f"Auto Length Rules: {self.auto_length_table.rowCount()} rules")
        
        self.preview_text.setText("\n".join(preview_lines))
        
        # Generate SQL preview
        sql_lines = [
            "-- BoltDefinition insert",
            f"INSERT INTO BoltDefinition (Name, StandardId, Diameter, ...) VALUES ('{bolt_name}', ...)",
            "",
            f"-- SetBolts inserts ({self.lengths_table.rowCount()} rows)",
            "INSERT INTO SetBolts (BoltDefId, Length, Weight, PartName) VALUES ...",
            "",
            f"-- SetOfBolts inserts ({selected_count} rows)",
            "INSERT INTO SetOfBolts (BoltDefId, SetId) VALUES ...",
        ]
        
        self.sql_preview.setText("\n".join(sql_lines))
        
    def create_bolt(self):
        """Create the bolt with all related data"""
        # Validate data
        if not self.name_input.text():
            QMessageBox.warning(self, "Validation Error", "Bolt name is required.")
            return
            
        if self.lengths_table.rowCount() == 0:
            QMessageBox.warning(self, "Validation Error", "At least one bolt length is required.")
            return
            
        selected_sets = [i for i in range(self.assembly_list.count()) 
                        if self.assembly_list.item(i).isSelected()]
        if not selected_sets:
            QMessageBox.warning(self, "Validation Error", "At least one assembly set must be selected.")
            return
            
        # Collect all data
        self.bolt_data = BoltData(
            name=self.name_input.text(),
            standard_id=self.standard_combo.currentData(),
            diameter=self.diameter_input.value(),
            strength_class_id=self.strength_combo.currentData(),
            author_id=self.author_combo.currentData(),
            head_diameter=self.head_diameter_input.value(),
            head_height=self.head_height_input.value()
        )
        
        # Collect lengths
        self.bolt_data.lengths = []
        for row in range(self.lengths_table.rowCount()):
            length = float(self.lengths_table.item(row, 0).text())
            weight = float(self.lengths_table.item(row, 1).text())
            part_name = self.lengths_table.item(row, 2).text()
            self.bolt_data.lengths.append((length, weight, part_name))
            
        # Collect assembly sets
        self.bolt_data.assembly_sets = []
        for i in selected_sets:
            set_id = self.assembly_list.item(i).data(Qt.UserRole)
            self.bolt_data.assembly_sets.append(set_id)
            
        self.accept()

class SchemaValidationWidget(QWidget):
    """Widget for validating database schema and relationships"""
    
    def __init__(self, cursor, parent=None):
        super().__init__(parent)
        self.cursor = cursor
        self.init_ui()
        
    def init_ui(self):
        layout = QVBoxLayout()
        
        # Validation options
        layout.addWidget(QLabel("Schema Validation Tools:"))
        
        # Check buttons
        btn_layout = QVBoxLayout()
        
        check_orphans_btn = QPushButton("Check for Orphaned Records")
        check_orphans_btn.clicked.connect(self.check_orphaned_records)
        btn_layout.addWidget(check_orphans_btn)
        
        check_missing_btn = QPushButton("Check Missing SetNutsBolts Data")
        check_missing_btn.clicked.connect(self.check_missing_nut_data)
        btn_layout.addWidget(check_missing_btn)
        
        check_incomplete_btn = QPushButton("Check Incomplete Bolt Definitions")
        check_incomplete_btn.clicked.connect(self.check_incomplete_bolts)
        btn_layout.addWidget(check_incomplete_btn)
        
        validate_lengths_btn = QPushButton("Validate AutoLength Coverage")
        validate_lengths_btn.clicked.connect(self.validate_auto_length)
        btn_layout.addWidget(validate_lengths_btn)
        
        layout.addLayout(btn_layout)
        
        # Results display
        self.results_text = QTextEdit()
        self.results_text.setReadOnly(True)
        layout.addWidget(self.results_text)
        
        self.setLayout(layout)
        
    def check_orphaned_records(self):
        """Check for orphaned records across tables"""
        results = ["=== ORPHANED RECORDS CHECK ===\n"]
        
        checks = [
            ("SetBolts without BoltDefinition",



def create_toolbar(self):
        """Create toolbar with common actions"""
        toolbar = QToolBar()
        toolbar.setMovable(False)
        
        # Refresh action
        refresh_action = toolbar.addAction("🔄 Refresh")
        refresh_action.triggered.connect(self.populate_table)
        
        # Export action
        export_action = toolbar.addAction("📥 Export")
        export_action.triggered.connect(self.export_to_csv)
        
        # Advanced search
        search_action = toolbar.addAction("🔍 Advanced Search")
        search_action.triggered.connect(self.show_advanced_search)
        
        toolbar.addSeparator()
        
        # Filter presets
        preset_action = toolbar.addAction("⭐ Filter Presets")
        preset_action.triggered.connect(self.show_filter_presets)
        
        # Save current filter
        save_filter_action = toolbar.addAction("💾 Save Filter")
        save_filter_action.triggered.connect(self.save_current_filter)
        
        toolbar.addSeparator()
        
        # Clear filters
        clear_action = toolbar.addAction("❌ Clear All Filters")
        clear_action.triggered.connect(self.clear_all_filters)
        
        # Data integrity check
        toolbar.addSeparator()
        integrity_action = toolbar.addAction("🔧 Check Integrity")
        integrity_action.triggered.connect(self.validate_data_integrity)
        
        # Update defaults reminder
        toolbar.addSeparator()
        update_action = toolbar.addAction("⚡ Update Defaults")
        update_action.setToolTip("Run this in Advance Steel after database changes")
        update_action.triggered.connect(self.show_update_defaults_reminder)
        
        return toolbar

    def create_status_bar(self):
        """Create status bar with connection and timing info"""
        status_bar = QStatusBar()
        
        # Connection status
        self.conn_status = QLabel("Disconnected")
        status_bar.addWidget(self.conn_status)
        
        # Query timing
        self.timing_label = QLabel("")
        status_bar.addWidget(self.timing_label)
        
        # Row count
        self.row_count_label = QLabel("")
        status_bar.addPermanentWidget(self.row_count_label)
        
        return status_bar

    def setup_shortcuts(self):
        """Setup keyboard shortcuts"""
        # Ctrl+F for filter focus
        QShortcut(QKeySequence("Ctrl+F"), self, 
                  lambda: self.filter_box.setFocus())
        
        # Ctrl+E for export
        QShortcut(QKeySequence("Ctrl+E"), self, self.export_to_csv)
        
        # F5 for refresh
        QShortcut(QKeySequence("F5"), self, self.populate_table)
        
        # Escape to clear filters
        QShortcut(QKeySequence("Escape"), self, self.clear_all_filters)
        
        # Ctrl+Shift+F for advanced search
        QShortcut(QKeySequence("Ctrl+Shift+F"), self, self.show_advanced_search)
        
        # Ctrl+N for new bolt
        QShortcut(QKeySequence("Ctrl+N"), self, self.show_bolt_creation_wizard)

    def connect_to_server(self):
        """Connect to SQL Server with error handling"""
        try:
            self.status_label.setText("Connecting...")
            self.connect_button.setEnabled(False)
            
            # Get selected database path
            selected_db = self.db_dropdown.currentText()
            
            # Save to session
            self.session_manager.config['last_database'] = selected_db
            self.session_manager.save_config()
            
            conn_str = (
                f"DRIVER={{{DB_CONFIG['driver']}}};"
                f"SERVER={DB_CONFIG['server']};"
                f"Trusted_Connection={DB_CONFIG['trusted_connection']};"
                f"AttachDbFilename={selected_db};"
            )
            
            self.connection = pyodbc.connect(conn_str)
            self.cursor = self.connection.cursor()
            
            self.status_label.setText("✅ Connected to SQL Server")
            self.conn_status.setText("✅ Connected")
            self.disconnect_button.setEnabled(True)
            self.load_table_button.setEnabled(True)
            
            # Enable creation and validation tools
            self.enable_tools()
            
            # Auto-load tables on successful connection
            self.load_tables()
            
            # Load recent custom bolts
            self.load_recent_custom_bolts()
            
        except Exception as e:
            error_msg = self.format_sql_error(e)
            self.status_label.setText("❌ Connection failed")
            self.conn_status.setText("❌ Disconnected")
            self.connect_button.setEnabled(True)
            QMessageBox.critical(self, "Connection Error", error_msg)

    def enable_tools(self):
        """Enable tools after connection"""
        # Creation tab
        self.creation_message.setText("✅ Connected - Bolt creation tools ready")
        self.create_bolt_btn.setEnabled(True)
        self.clone_bolt_btn.setEnabled(True)
        self.add_length_btn.setEnabled(True)
        
        # Validation tab
        self.validation_message.setText("✅ Connected - Validation tools ready")
        if not self.validation_widget:
            self.validation_widget = SchemaValidationWidget(self.cursor, self)
            self.validation_container.addWidget(self.validation_widget)

    def format_sql_error(self, error):
        """Format SQL errors for user display"""
        error_str = str(error)
        
        # Common error patterns
        if "permission" in error_str.lower():
            return "Access denied. Please check your database permissions."
        elif "timeout" in error_str.lower():
            return "Query timeout. Try applying filters to reduce data size."
        elif "syntax" in error_str.lower():
            return "Invalid query syntax. This might be a bug - please report it."
        elif "localdb" in error_str.lower() and "not found" in error_str.lower():
            return "LocalDB instance not found. Please ensure Advance Steel is properly installed."
        else:
            return f"Database error: {error_str[:200]}..."

    def disconnect_from_server(self):
        """Disconnect from SQL Server"""
        try:
            if self.connection:
                self.connection.close()
        except Exception as e:
            print(f"Error during disconnect: {e}")
        finally:
            self.connection = None
            self.cursor = None
            self.status_label.setText("Disconnected")
            self.conn_status.setText("Disconnected")
            self.connect_button.setEnabled(True)
            self.disconnect_button.setEnabled(False)
            self.load_table_button.setEnabled(False)
            self.filter_box.setEnabled(False)
            self.unit_toggle.setEnabled(False)
            self.prev_button.setEnabled(False)
            self.next_button.setEnabled(False)
            
            # Disable tools
            self.creation_message.setText("Connect to database to enable bolt creation tools.")
            self.create_bolt_btn.setEnabled(False)
            self.clone_bolt_btn.setEnabled(False)
            self.add_length_btn.setEnabled(False)
            
            self.validation_message.setText("Connect to database to enable validation tools.")
            
            # Clear UI
            self.table_list.clear()
            self.data_table.clear()
            self.page_info_label.setText("No data loaded")
            self.row_count_label.setText("")
            self.table_info_label.setText("")

    def is_connected(self):
        """Check if database connection is active"""
        return self.connection is not None and self.cursor is not None

    def load_tables(self):
        """Load tables in background thread"""
        if not self.is_connected():
            QMessageBox.warning(self, "No Connection", "Please connect to the database first.")
            return
        
        self.progress_bar.setVisible(True)
        self.progress_bar.setRange(0, 0)  # Indeterminate progress
        self.load_table_button.setEnabled(False)
        
        # Use background thread to avoid UI freezing
        self.table_loader = TableLoader(self.cursor)
        self.table_loader.tables_loaded.connect(self.on_tables_loaded)
        self.table_loader.error_occurred.connect(self.on_table_load_error)
        self.table_loader.start()

    def on_tables_loaded(self, tables):
        """Handle successful table loading"""
        self.tables = tables
        self.table_list.clear()
        
        # Get recent tables
        recent_tables = self.session_manager.config.get('recent_tables', [])
        
        # Group tables by function
        table_groups = {
            'Core Tables': ['BoltDefinition', 'SetBolts', 'SetOfBolts', 'Standard', 'Sets'],
            'Support Tables': ['SetNutsBolts', 'StrengthClass', 'Authors', 'AutoLength'],
            'Other': []
        }
        
        # Categorize tables
        for table in self.tables:
            categorized = False
            for group, group_tables in table_groups.items():
                if table in group_tables:
                    categorized = True
                    break
            if not categorized:
                table_groups['Other'].append(table)
        
        # Add tables with grouping and recent highlighting
        for group_name, group_tables in table_groups.items():
            if group_tables:
                # Add group header
                header_item = QListWidgetItem(f"--- {group_name} ---")
                header_item.setFlags(Qt.NoItemFlags)
                header_item.setBackground(QColor(240, 240, 240))
                font = header_item.font()
                font.setBold(True)
                header_item.setFont(font)
                self.table_list.addItem(header_item)
                
                # Add tables in group
                for table in sorted(group_tables):
                    if table in self.tables:
                        item = QListWidgetItem(f"  {table}")
                        if table in recent_tables[:5]:  # Highlight top 5 recent
                            item.setToolTip(f"Recently accessed (#{recent_tables.index(table) + 1})")
                            # Add a star for recent tables
                            item.setText(f"  ⭐ {table}")
                        
                        # Add schema info to tooltip
                        if table in BOLT_SCHEMA:
                            schema_info = BOLT_SCHEMA[table]
                            tooltip = f"{schema_info['description']}\n"
                            if schema_info['foreign_keys']:
                                tooltip += f"Foreign keys: {', '.join(schema_info['foreign_keys'].keys())}"
                            item.setToolTip(tooltip)
                        
                        self.table_list.addItem(item)
        
        self.progress_bar.setVisible(False)
        self.load_table_button.setEnabled(True)
        self.filter_box.setEnabled(True)
        self.unit_toggle.setEnabled(True)

    def on_table_load_error(self, error_msg):
        """Handle table loading error"""
        self.progress_bar.setVisible(False)
        self.load_table_button.setEnabled(True)
        QMessageBox.critical(self, "Table Load Error", f"Failed to load tables: {error_msg}")

    @ensure_connection
    def load_table_data(self, item):
        """Load data for selected table"""
        if not self.is_connected():
            return
        
        # Skip group headers
        if item.flags() == Qt.NoItemFlags:
            return
        
        # Remove star prefix and indentation if present
        table_name = item.text().strip().replace("⭐ ", "")
        
        # Validate table name against known tables
        if table_name not in FASTENER_TABLES:
            QMessageBox.warning(self, "Invalid Table", f"Table '{table_name}' is not a recognized fastener table.")
            return
        
        self.current_table = table_name
        self.page = 0
        self.sort_column = None
        self.sort_order = "ASC"
        self.column_filters = {}
        self.advanced_conditions = []
        
        # Update table info
        if table_name in BOLT_SCHEMA:
            info = BOLT_SCHEMA[table_name]
            info_text = f"<b>{info['description']}</b><br>"
            if info['foreign_keys']:
                info_text += "References: " + ", ".join([f"{k}→{v}" for k, v in info['foreign_keys'].items()])
            self.table_info_label.setText(info_text)
        else:
            self.table_info_label.setText("")
        
        # Track in session
        self.session_manager.add_recent_table(table_name)
        
        self.populate_table()

    def build_where_clause(self):
        """Build WHERE clause for both global and column-specific filters"""
        where_conditions = []
        params = []
        
        # Validate table name first
        if self.current_table not in FASTENER_TABLES:
            raise ValueError(f"Invalid table name: {self.current_table}")
        
        # Get all columns for the table
        self.cursor.execute(f"SELECT COLUMN_NAME FROM INFORMATION_SCHEMA.COLUMNS WHERE TABLE_NAME = ?", (self.current_table,))
        all_columns = [row[0] for row in self.cursor.fetchall()]
        
        # Advanced search conditions
        if self.advanced_conditions:
            for condition in self.advanced_conditions:
                col = condition['column']
                op = condition['operator']
                val = condition['value']
                
                if op == 'contains':
                    where_conditions.append(f"CAST([{col}] AS NVARCHAR(MAX)) LIKE ?")
                    params.append(f"%{val}%")
                elif op == 'equals':
                    where_conditions.append(f"CAST([{col}] AS NVARCHAR(MAX)) = ?")
                    params.append(val)
                elif op == 'starts with':
                    where_conditions.append(f"CAST([{col}] AS NVARCHAR(MAX)) LIKE ?")
                    params.append(f"{val}%")
                elif op == 'ends with':
                    where_conditions.append(f"CAST([{col}] AS NVARCHAR(MAX)) LIKE ?")
                    params.append(f"%{val}")
                elif op == 'not contains':
                    where_conditions.append(f"CAST([{col}] AS NVARCHAR(MAX)) NOT LIKE ?")
                    params.append(f"%{val}%")
        else:
            # Global filter (search box) - only if no advanced conditions
            keyword = self.filter_box.text().strip()
            if keyword:
                global_conditions = []
                for col in all_columns:
                    global_conditions.append(f"CAST([{col}] AS NVARCHAR(MAX)) LIKE ?")
                    params.append(f"%{keyword}%")
                where_conditions.append(f"({' OR '.join(global_conditions)})")
        
        # Column-specific filters
        for col_name, filter_value in self.column_filters.items():
            if filter_value and filter_value != "All":
                where_conditions.append(f"CAST([{col_name}] AS NVARCHAR(MAX)) LIKE ?")
                params.append(f"%{filter_value}%")
        
        where_clause = " AND ".join(where_conditions) if where_conditions else ""
        return where_clause, params

    @ensure_connection
    def get_filtered_count(self):
        """Get total count of filtered rows"""
        if not self.is_connected() or not self.current_table:
            return 0
        
        try:
            where_clause, params = self.build_where_clause()
            
            if where_clause:
                query = f"SELECT COUNT(*) FROM [{self.current_table}] WHERE {where_clause}"
                self.cursor.execute(query, params)
            else:
                query = f"SELECT COUNT(*) FROM [{self.current_table}]"
                self.cursor.execute(query)
            
            return self.cursor.fetchone()[0]
        except Exception as e:
            print(f"Error getting filtered count: {e}")
            return 0

    @ensure_connection
    @time_it
    def populate_table(self):
        """Populate table with server-side pagination, filtering, and sorting"""
        if not self.is_connected() or not self.current_table:
            return

        try:
            # Get total filtered count
            self.total_filtered_rows = self.get_filtered_count()
            
            # Update row count in status bar
            self.row_count_label.setText(f"Total rows: {self.total_filtered_rows}")
            
            # Build query with filtering, sorting, and pagination
            where_clause, params = self.build_where_clause()
            offset = self.page * self.rows_per_page
            
            # Build ORDER BY clause
            order_clause = ""
            if self.sort_column:
                order_clause = f"ORDER BY [{self.sort_column}] {self.sort_order}"
            else:
                order_clause = "ORDER BY (SELECT NULL)"
            
            # Build complete query
            if where_clause:
                query = f"""
                    SELECT * FROM [{self.current_table}] 
                    WHERE {where_clause}
                    {order_clause}
                    OFFSET ? ROWS 
                    FETCH NEXT ? ROWS ONLY
                """
                params.extend([offset, self.rows_per_page])
                self.cursor.execute(query, params)
            else:
                query = f"""
                    SELECT * FROM [{self.current_table}]
                    {order_clause}
                    OFFSET ? ROWS 
                    FETCH NEXT ? ROWS ONLY
                """
                self.cursor.execute(query, (offset, self.rows_per_page))

            # Get results
            rows = self.cursor.fetchall()
            if not rows:
                columns = []
            else:
                columns = [col[0] for col in self.cursor.description]

            # Update table widget
            self.data_table.setColumnCount(len(columns))
            self.data_table.setRowCount(len(rows))
            if columns:
                self.setup_column_headers(columns)

            # Highlight foreign key columns
            foreign_key_cols = []
            if self.current_table in BOLT_SCHEMA:
                foreign_key_cols = list(BOLT_SCHEMA[self.current_table]['foreign_keys'].keys())

            for i, row in enumerate(rows):
                for j, val in enumerate(row):
                    if val is None:
                        display_val = ""
                    else:
                        # Apply unit conversion if needed
                        if (self.convert_to_inches and 
                            j < len(columns) and 
                            columns[j] in UNIT_CONVERT and 
                            isinstance(val, (float, int))):
                            display_val = str(round(val / MM_TO_INCH, 3))
                        else:
                            display_val = str(val)
                    
                    item = QTableWidgetItem(display_val)
                    
                    # Highlight foreign key columns
                    if columns[j] in foreign_key_cols:
                        item.setBackground(QColor(240, 240, 255))
                        item.setToolTip(f"Foreign key to {BOLT_SCHEMA[self.current_table]['foreign_keys'][columns[j]]}")
                    
                    self.data_table.setItem(i, j, item)

            # Update pagination info
            start_row = offset + 1 if rows else 0
            end_row = min(offset + len(rows), self.total_filtered_rows)
            self.page_info_label.setText(f"Showing {start_row}-{end_row} of {self.total_filtered_rows} rows")
            
            # Update button states
            self.prev_button.setEnabled(self.page > 0)
            self.next_button.setEnabled(end_row < self.total_filtered_rows)

        except Exception as e:
            error_msg = self.format_sql_error(e)
            QMessageBox.critical(self, "Data Load Error", error_msg)

    def setup_column_headers(self, columns):
        """Setup column headers with sort indicators"""
        headers = []
        for col in columns:
            header_text = col
            if self.sort_column == col:
                if self.sort_order == "ASC":
                    header_text += " ↑"
                else:
                    header_text += " ↓"
            
            # Add filter indicator if column has filter
            if col in self.column_filters and self.column_filters[col]:
                header_text += " 🔍"
            
            headers.append(header_text)
        
        self.data_table.setHorizontalHeaderLabels(headers)

    def on_header_clicked(self, logical_index):
        """Handle column header clicks for sorting"""
        if not self.is_connected() or not self.current_table:
            return
        
        # Get column name
        self.cursor.execute(f"SELECT COLUMN_NAME FROM INFORMATION_SCHEMA.COLUMNS WHERE TABLE_NAME = ? ORDER BY ORDINAL_POSITION", (self.current_table,))
        columns = [row[0] for row in self.cursor.fetchall()]
        
        if logical_index < len(columns):
            column_name = columns[logical_index]
            
            # Toggle sort order if same column, otherwise set to ASC
            if self.sort_column == column_name:
                self.sort_order = "DESC" if self.sort_order == "ASC" else "ASC"
            else:
                self.sort_column = column_name
                self.sort_order = "ASC"
            
            # Reset to first page and refresh
            self.page = 0
            self.populate_table()

    def show_column_filter_menu(self, position):
        """Show improved context menu for column filtering with scrolling support"""
        if not self.is_connected() or not self.current_table:
            return
        
        # Get the column index at the clicked position
        logical_index = self.data_table.horizontalHeader().logicalIndexAt(position)
        if logical_index < 0:
            return
        
        # Get column name
        self.cursor.execute(f"SELECT COLUMN_NAME FROM INFORMATION_SCHEMA.COLUMNS WHERE TABLE_NAME = ? ORDER BY ORDINAL_POSITION", (self.current_table,))
        columns = [row[0] for row in self.cursor.fetchall()]
        
        if logical_index >= len(columns):
            return
        
        column_name = columns[logical_index]
        current_filter = self.column_filters.get(column_name, "")
        
        # Get unique values for this column
        try:
            query = f"SELECT DISTINCT CAST([{column_name}] AS NVARCHAR(MAX)) as val FROM [{self.current_table}] WHERE [{column_name}] IS NOT NULL ORDER BY val"
            self.cursor.execute(query)
            unique_values = [row[0] for row in self.cursor.fetchall() if row[0]]
            
            if len(unique_values) > 50:  # Use dialog for large lists
                dialog = ScrollableFilterDialog(column_name, unique_values, current_filter, self)
                dialog.filter_selected.connect(lambda value: self.set_column_filter(column_name, value))
                dialog.exec_()
            else:
                # Use scrollable menu for smaller lists
                menu = ScrollableMenu(max_visible_items=15, parent=self)
                
                # Prepare actions data
                actions_data = [("All (Clear Filter)", lambda: self.set_column_filter(column_name, ""))]
                
                for value in unique_values:
                    display_text = str(value)
                    if str(value) == str(current_filter):
                        display_text = f"✓ {display_text}"
                    actions_data.append((display_text, lambda v=value: self.set_column_filter(column_name, v)))
                
                menu.add_scrollable_actions(actions_data)
                
                # Show menu at clicked position
                global_pos = self.data_table.horizontalHeader().mapToGlobal(position)
                menu.exec_(global_pos)
        
        except Exception as e:
            QMessageBox.warning(self, "Filter Error", f"Error loading filter options: {str(e)}")

    def set_column_filter(self, column_name, filter_value):
        """Set filter for a specific column"""
        if filter_value:
            self.column_filters[column_name] = filter_value
        else:
            # Remove filter
            self.column_filters.pop(column_name, None)
        
        # Reset to first page and refresh
        self.page = 0
        self.populate_table()

    def show_row_context_menu(self, position):
        """Show context menu for selected rows"""
        selected_rows = set(item.row() for item in self.data_table.selectedItems())
        
        if not selected_rows:
            return
        
        menu = QMenu()
        
        # Export selected rows
        export_action = menu.addAction(f"📥 Export {len(selected_rows)} selected rows")
        export_action.triggered.connect(lambda: self.export_selected_rows(selected_rows))
        
        # Copy to clipboard
        copy_action = menu.addAction(f"📋 Copy {len(selected_rows)} rows to clipboard")
        copy_action.triggered.connect(lambda: self.copy_rows_to_clipboard(selected_rows))
        
        # If viewing BoltDefinition table, add bolt-specific actions
        if self.current_table == "BoltDefinition" and len(selected_rows) == 1:
            menu.addSeparator()
            
            # View related data
            view_lengths_action = menu.addAction("🔍 View Bolt Lengths")
            view_lengths_action.triggered.connect(lambda: self.view_related_data("SetBolts", list(selected_rows)[0]))
            
            view_sets_action = menu.addAction("🔍 View Assembly Sets")
            view_sets_action.triggered.connect(lambda: self.view_related_data("SetOfBolts", list(selected_rows)[0]))
            
            # Clone bolt
            clone_action = menu.addAction("📋 Clone This Bolt")
            clone_action.triggered.connect(lambda: self.clone_bolt_from_selection(list(selected_rows)[0]))
        
        menu.exec_(self.data_table.viewport().mapToGlobal(position))

    def view_related_data(self, target_table, row_index):
        """View related data for a selected bolt"""
        if not self.is_connected() or row_index >= self.data_table.rowCount():
            return
        
        # Get the ID of the selected bolt
        bolt_id = None
        for col in range(self.data_table.columnCount()):
            header = self.data_table.horizontalHeaderItem(col).text().split(" ")[0]
            if header == "ID":
                bolt_id = self.data_table.item(row_index, col).text()
                break
        
        if not bolt_id:
            QMessageBox.warning(self, "No ID", "Could not find bolt ID.")
            return
        
        # Switch to target table with filter
        for i in range(self.table_list.count()):
            item = self.table_list.item(i)
            if target_table in item.text():
                self.table_list.setCurrentItem(item)
                self.current_table = target_table
                self.column_filters = {"BoltDefId": bolt_id}
                self.page = 0
                self.populate_table()
                break

    def clear_all_filters(self):
        """Clear all column filters"""
        self.column_filters = {}
        self.advanced_conditions = []
        self.filter_box.clear()
        self.page = 0
        self.populate_table()

    def change_page(self, direction):
        """Change page with bounds checking"""
        new_page = self.page + direction
        max_page = (self.total_filtered_rows - 1) // self.rows_per_page if self.total_filtered_rows > 0 else 0
        
        if 0 <= new_page <= max_page:
            self.page = new_page
            self.populate_table()

    def apply_filter(self):
        """Apply filter and reset to first page"""
        self.page = 0
        self.advanced_conditions = []  # Clear advanced search when using global filter
        self.populate_table()

    def toggle_units(self):
        """Toggle between metric and imperial units"""
        self.convert_to_inches = self.unit_toggle.isChecked()
        self.populate_table()

    def show_advanced_search(self):
        """Show advanced search dialog"""
        if not self.is_connected() or not self.current_table:
            QMessageBox.warning(self, "No Table Selected", "Please select a table first.")
            return
        
        # Get columns
        self.cursor.execute(f"SELECT COLUMN_NAME FROM INFORMATION_SCHEMA.COLUMNS WHERE TABLE_NAME = ?", (self.current_table,))
        columns = [row[0] for row in self.cursor.fetchall()]
        
        dialog = AdvancedSearchDialog(columns, self)
        if dialog.exec_():
            self.advanced_conditions = dialog.get_conditions()
            self.filter_box.clear()  # Clear global filter when using advanced search
            self.page = 0
            self.populate_table()

    def export_to_csv(self):
        """Export current view to CSV"""
        if not self.is_connected() or not self.current_table:
            QMessageBox.warning(self, "No Data", "Please load a table first.")
            return
        
        filename, _ = QFileDialog.getSaveFileName(
            self, "Export to CSV", f"{self.current_table}_export.csv", "CSV Files (*.csv)"
        )
        
        if filename:
            try:
                # Get current filtered data (all rows, not just current page)
                where_clause, params = self.build_where_clause()
                
                # Build ORDER BY clause
                order_clause = ""
                if self.sort_column:
                    order_clause = f"ORDER BY [{self.sort_column}] {self.sort_order}"
                
                if where_clause:
                    query = f"SELECT * FROM [{self.current_table}] WHERE {where_clause} {order_clause}"
                    self.cursor.execute(query, params)
                else:
                    query = f"SELECT * FROM [{self.current_table}] {order_clause}"
                    self.cursor.execute(query)
                
                rows = self.cursor.fetchall()
                columns = [col[0] for col in self.cursor.description]
                
                with open(filename, 'w', newline='', encoding='utf-8') as f:
                    writer = csv.writer(f)
                    
                    # Write headers with unit indication
                    if self.convert_to_inches:
                        headers = []
                        for col in columns:
                            if col in UNIT_CONVERT:
                                headers.append(f"{col} (inches)")
                            else:
                                headers.append(col)
                        writer.writerow(headers)
                    else:
                        writer.writerow(columns)
                    
                    # Write data with unit conversion if needed
                    for row in rows:
                        converted_row = []
                        for j, val in enumerate(row):
                            if val is None:
                                converted_row.append("")
                            elif (self.convert_to_inches and 
                                  j < len(columns) and 
                                  columns[j] in UNIT_CONVERT and 
                                  isinstance(val, (float, int))):
                                converted_row.append(round(val / MM_TO_INCH, 3))
                            else:
                                converted_row.append(val)
                        writer.writerow(converted_row)
                
                QMessageBox.information(self, "Export Complete", 
                                      f"Exported {len(rows)} rows to {filename}")
            except Exception as e:
                QMessageBox.critical(self, "Export Error", self.format_sql_error(e))

    def export_selected_rows(self, selected_rows):
        """Export only selected rows to CSV"""
        if not self.data_table.columnCount():
            return
        
        filename, _ = QFileDialog.getSaveFileName(
            self, "Export Selected Rows", f"{self.current_table}_selection.csv", "CSV Files (*.csv)"
        )
        
        if filename:
            try:
                with open(filename, 'w', newline='', encoding='utf-8') as f:
                    writer = csv.writer(f)
                    
                    # Write headers
                    headers = []
                    for col in range(self.data_table.columnCount()):
                        headers.append(self.data_table.horizontalHeaderItem(col).text().split(" ")[0])
                    writer.writerow(headers)
                    
                    # Write selected rows
                    for row in sorted(selected_rows):
                        row_data = []
                        for col in range(self.data_table.columnCount()):
                            item = self.data_table.item(row, col)
                            row_data.append(item.text() if item else "")
                        writer.writerow(row_data)
                
                QMessageBox.information(self, "Export Complete", 
                                      f"Exported {len(selected_rows)} rows to {filename}")
            except Exception as e:
                QMessageBox.critical(self, "Export Error", str(e))

    def copy_rows_to_clipboard(self, selected_rows):
        """Copy selected rows to clipboard"""
        from PyQt5.QtWidgets import QApplication
        
        if not self.data_table.columnCount():
            return
        
        # Build text representation
        text_lines = []
        
        # Headers
        headers = []
        for col in range(self.data_table.columnCount()):
            headers.append(self.data_table.horizontalHeaderItem(col).text().split(" ")[0])
        text_lines.append("\t".join(headers))
        
        # Data
        for row in sorted(selected_rows):
            row_data = []
            for col in range(self.data_table.columnCount()):
                item = self.data_table.item(row, col)
                row_data.append(item.text() if item else "")
            text_lines.append("\t".join(row_data))
        
        # Copy to clipboard
        clipboard_text = "\n".join(text_lines)
        QApplication.clipboard().setText(clipboard_text)
        
        QMessageBox.information(self, "Copied", 
                              f"Copied {len(selected_rows)} rows to clipboard")

    def show_filter_presets(self):
        """Show and apply saved filter presets"""
        if not self.current_table:
            QMessageBox.warning(self, "No Table", "Please select a table first.")
            return
        
        presets = self.session_manager.get_filter_presets(self.current_table)
        
        if not presets:
            QMessageBox.information(self, "No Presets", 
                                  "No saved filter presets for this table.")
            return
        
        menu = QMenu()
        
        for name, preset_data in presets.items():
            action = menu.addAction(name)
            action.triggered.connect(lambda checked, p=preset_data: self.apply_filter_preset(p))
        
        menu.addSeparator()
        manage_action = menu.addAction("Manage Presets...")
        manage_action.triggered.connect(self.manage_filter_presets)
        
        menu.exec_(self.mapToGlobal(self.toolbar.pos()))

    def apply_filter_preset(self, preset_data):
        """Apply a saved filter preset"""
        self.filter_box.setText(preset_data.get('global_filter', ''))
        self.column_filters = preset_data.get('column_filters', {})
        self.page = 0
        self.populate_table()

    def save_current_filter(self):
        """Save current filter configuration as a preset"""
        if not self.current_table:
            return
        
        if not self.filter_box.text() and not self.column_filters and not self.advanced_conditions:
            QMessageBox.information(self, "No Filters", 
                                  "No filters are currently active.")
            return
        
        from PyQt5.QtWidgets import QInputDialog
        
        name, ok = QInputDialog.getText(self, "Save Filter Preset", 
                                       "Enter a name for this filter preset:")
        
        if ok and name:
            self.session_manager.save_filter_preset(
                name, 
                self.current_table, 
                self.filter_box.text(),
                self.column_filters
            )
            QMessageBox.information(self, "Saved", 
                                  f"Filter preset '{name}' saved successfully.")

    def manage_filter_presets(self):
        """Manage saved filter presets"""
        # This would open a dialog to delete/rename presets
        # For now, just show a message
        QMessageBox.information(self, "Manage Presets", 
                              "Preset management coming soon!\n\n"
                              "Presets are saved in bolt_manager_config.json")

    def validate_data_integrity(self):
        """Run integrity checks on current table"""
        if not self.is_connected() or not self.current_table:
            QMessageBox.warning(self, "No Table", "Please select a table first.")
            return
        
        checks = []
        
        try:
            # Check total row count
            self.cursor.execute(f"SELECT COUNT(*) FROM [{self.current_table}]")
            total_rows = self.cursor.fetchone()[0]
            checks.append(f"Total rows: {total_rows}")
            
            # Check for null values in each column
            self.cursor.execute(f"SELECT COLUMN_NAME FROM INFORMATION_SCHEMA.COLUMNS WHERE TABLE_NAME = ?", (self.current_table,))
            columns = [row[0] for row in self.cursor.fetchall()]
            
            null_counts = []
            for col in columns[:5]:  # Check first 5 columns to avoid long wait
                self.cursor.execute(f"SELECT COUNT(*) FROM [{self.current_table}] WHERE [{col}] IS NULL")
                null_count = self.cursor.fetchone()[0]
                if null_count > 0:
                    null_counts.append(f"{col}: {null_count} nulls")
            
            if null_counts:
                checks.append("\nNull value counts:")
                checks.extend(null_counts)
            
            # Table-specific checks based on schema
            if self.current_table in BOLT_SCHEMA:
                schema_info = BOLT_SCHEMA[self.current_table]
                
                # Check foreign keys
                for fk_col, ref_table in schema_info['foreign_keys'].items():
                    query = f"""
                        SELECT COUNT(*) FROM [{self.current_table}] t
                        LEFT JOIN [{ref_table}] r ON t.[{fk_col}] = r.ID
                        WHERE t.[{fk_col}] IS NOT NULL AND r.ID IS NULL
                    """
                    try:
                        self.cursor.execute(query)
                        orphaned = self.cursor.fetchone()[0]
                        if orphaned > 0:
                            checks.append(f"\nOrphaned {fk_col} references: {orphaned}")
                    except:
                        pass
            
            # Show results
            message = "\n".join(checks)
            QMessageBox.information(self, "Data Integrity Check", message)
            
        except Exception as e:
            QMessageBox.critical(self, "Validation Error", self.format_sql_error(e))

    def show_update_defaults_reminder(self):
        """Show reminder about updating defaults in Advance Steel"""
        msg = QMessageBox()
        msg.setIcon(QMessageBox.Information)
        msg.setWindowTitle("Update Defaults Reminder")
        msg.setText("After making database changes, remember to:")
        msg.setInformativeText(
            "1. Save and close this tool\n"
            "2. Open Advance Steel\n"
            "3. Go to Home tab → Management Tools\n"
            "4. Click 'Update Defaults'\n\n"
            "Or run command: _AstMgmUpdateValues"
        )
        msg.exec_()

    def show_bolt_creation_wizard(self):
        """Show the bolt creation wizard"""
        if not self.is_connected():
            QMessageBox.warning(self, "No Connection", "Please connect to the database first.")
            return
        
        wizard = BoltCreationWizard(self.cursor, self)
        if wizard.exec_():
            # Create the bolt
            bolt_data = wizard.bolt_data
            
            try:
                with DatabaseTransaction(self.connection) as cursor:
                    # Insert BoltDefinition
                    insert_query = """
                        INSERT INTO BoltDefinition 
                        (Name, StandardId, Diameter, StrengthClassId, AuthorId, 
                         HeadDiameter, HeadHeight, ThreadType)
                        OUTPUT INSERTED.ID
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    """
                    cursor.execute(insert_query, (
                        bolt_data.name,
                        bolt_data.standard_id,
                        bolt_data.diameter,
                        bolt_data.strength_class_id,
                        bolt_data.author_id,
                        bolt_data.head_diameter,
                        bolt_data.head_height,
                        bolt_data.thread_type
                    ))
                    
                    bolt_def_id = cursor.fetchone()[0]
                    
                    # Insert SetBolts (lengths)
                    for length, weight, part_name in bolt_data.lengths:
                        cursor.execute(
                            "INSERT INTO SetBolts (BoltDefId, Length, Weight, PartName) VALUES (?, ?, ?, ?)",
                            (bolt_def_id, length, weight, part_name)
                        )
                    
                    # Insert SetOfBolts (assembly sets)
                    for set_id in bolt_data.assembly_sets:
                        cursor.execute(
                            "INSERT INTO SetOfBolts (BoltDefId, SetId) VALUES (?, ?)",
                            (bolt_def_id, set_id)
                        )
                    
                    # Track in session
                    self.session_manager.add_custom_bolt({
                        'name': bolt_data.name,
                        'standard': wizard.standard_combo.currentText(),
                        'diameter': bolt_data.diameter
                    })
                    
                    # Success message
                    QMessageBox.information(
                        self, "Success",
                        f"Bolt '{bolt_data.name}' created successfully!\n\n"
                        "Remember to run 'Update Defaults' in Advance Steel."
                    )
                    
                    # Refresh if viewing relevant table
                    if self.current_table in ["BoltDefinition", "SetBolts", "SetOfBolts"]:
                        self.populate_table()
                    
                    # Update recent bolts list
                    self.load_recent_custom_bolts()
                    
            except Exception as e:
                QMessageBox.critical(self, "Creation Error", 
                                   f"Failed to create bolt: {self.format_sql_error(e)}")

    def clone_existing_bolt(self):
        """Clone an existing bolt"""
        if not self.is_connected():
            return
        
        # Get list of bolts
        try:
            self.cursor.execute("SELECT ID, Name FROM BoltDefinition ORDER BY Name")
            bolts = self.cursor.fetchall()
            
            if not bolts:
                QMessageBox.information(self, "No Bolts", "No bolts found in database.")
                return
            
            # Create selection dialog
            from PyQt5.QtWidgets import QInputDialog
            
            bolt_names = [f"{name} (ID: {id})" for id, name in bolts]
            selected, ok = QInputDialog.getItem(
                self, "Clone Bolt", "Select bolt to clone:", bolt_names, 0, False
            )
            
            if ok and selected:
                # Extract ID from selection
                bolt_id = int(selected.split("ID: ")[1].split(")")[0])
                
                # Get new name
                new_name, ok = QInputDialog.getText(
                    self, "Clone Bolt", "Enter name for cloned bolt:"
                )
                
                if ok and new_name:
                    self.perform_bolt_clone(bolt_id, new_name)
                    
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to load bolts: {str(e)}")

    def perform_bolt_clone(self, source_bolt_id, new_name):
        """Perform the actual bolt cloning"""
        try:
            with DatabaseTransaction(self.connection) as cursor:
                # Get source bolt data
                cursor.execute("SELECT * FROM BoltDefinition WHERE ID = ?", (source_bolt_id,))
                source_data = cursor.fetchone()
                
                if not source_data:
                    raise ValueError("Source bolt not found")
                
                # Get column names
                cursor.execute("SELECT COLUMN_NAME FROM INFORMATION_SCHEMA.COLUMNS WHERE TABLE_NAME = 'BoltDefinition' ORDER BY ORDINAL_POSITION")
                columns = [row[0] for row in cursor.fetchall()]
                
                # Prepare insert data (exclude ID, change Name)
                insert_cols = [col for col in columns if col != 'ID']
                insert_vals = []
                
                for i, col in enumerate(columns):
                    if col == 'ID':
                        continue
                    elif col == 'Name':
                        insert_vals.append(new_name)
                    else:
                        insert_vals.append(source_data[i])
                
                # Insert new bolt definition
                placeholders = ','.join(['?' for _ in insert_cols])
                col_names = ','.join([f"[{col}]" for col in insert_cols])
                
                cursor.execute(
                    f"INSERT INTO BoltDefinition ({col_names}) OUTPUT INSERTED.ID VALUES ({placeholders})",
                    insert_vals
                )
                
                new_bolt_id = cursor.fetchone()[0]
                
                # Clone SetBolts
                cursor.execute(
                    """
                    INSERT INTO SetBolts (BoltDefId, Length, Weight, PartName)
                    SELECT ?, Length, Weight, PartName
                    FROM SetBolts WHERE BoltDefId = ?
                    """,
                    (new_bolt_id, source_bolt_id)
                )
                
                # Clone SetOfBolts
                cursor.execute(
                    """
                    INSERT INTO SetOfBolts (BoltDefId, SetId)
                    SELECT ?, SetId
                    FROM SetOfBolts WHERE BoltDefId = ?
                    """,
                    (new_bolt_id, source_bolt_id)
                )
                
                # Clone AutoLength if exists
                cursor.execute(
                    """
                    INSERT INTO AutoLength (BoltDefId, GripMin, GripMax, Length)
                    SELECT ?, GripMin, GripMax, Length
                    FROM AutoLength WHERE BoltDefId = ?
                    """,
                    (new_bolt_id, source_bolt_id)
                )
                
                QMessageBox.information(
                    self, "Success",
                    f"Bolt cloned successfully as '{new_name}'!\n\n"
                    "Remember to run 'Update Defaults' in Advance Steel."
                )
                
                # Refresh if viewing relevant table
                if self.current_table in ["BoltDefinition", "SetBolts", "SetOfBolts"]:
                    self.populate_table()
                    
        except Exception as e:
            QMessageBox.critical(self, "Clone Error", 
                               f"Failed to clone bolt: {self.format_sql_error(e)}")

    def clone_bolt_from_selection(self, row_index):
        """Clone bolt from table selection"""
        if not self.is_connected() or row_index >= self.data_table.rowCount():
            return
        
        # Get the ID and Name of the selected bolt
        bolt_id = None
        bolt_name = None
        
        for col in range(self.data_table.columnCount()):
            header = self.data_table.horizontalHeaderItem(col).text().split(" ")[0]
            if header == "ID":
                bolt_id = int(self.data_table.item(row_index, col).text())
            elif header == "Name":
                bolt_name = self.data_table.item(row_index, col).text()
        
        if bolt_id:
            # Get new name
            from PyQt5.QtWidgets import QInputDialog
            
            suggested_name = f"{bolt_name} Copy" if bolt_name else "New Bolt"
            new_name, ok = QInputDialog.getText(
                self, "Clone Bolt", 
                "Enter name for cloned bolt:",
                text=suggested_name
            )
            
            if ok and new_name:
                self.perform_bolt_clone(bolt_id, new_name)

    def add_bolt_length(self):
        """Add a new length to an existing bolt"""
        if not self.is_connected():
            return
        
        # Implementation similar to clone_existing_bolt but for adding lengths
        QMessageBox.information(self, "Coming Soon", 
                              "Add bolt length feature will be implemented soon.")

    def load_recent_custom_bolts(self):
        """Load recent custom bolts into the list"""
        self.recent_bolts_list.clear()
        
        custom_bolts = self.session_manager.config.get('custom_bolts', [])
        for bolt in custom_bolts[-10:]:  # Show last 10
            item_text = f"{bolt['name']} ({bolt['standard']}, Ø{bolt['diameter']}mm)"
            item = QListWidgetItem(item_text)
            item.setToolTip(f"Created: {bolt['created']}")
            self.recent_bolts_list.addItem(item)

    def cleanup(self):
        """Cleanup resources on exit"""
        if self.connection:
            try:
                self.connection.close()
            except:
                pass

    def closeEvent(self, event):
        """Handle window close event"""
        self.cleanup()
        event.accept()

if __name__ == '__main__':
    app = QApplication(sys.argv)
    manager = BoltManager()
    manager.resize(1400, 900)
    manager.show()
    sys.exit(app.exec_())        self.results_text.setText("\n".join(results))

def time_it(func):
    """Decorator to measure query execution time"""
    @wraps(func)
    def wrapper(self, *args, **kwargs):
        start = time.time()
        result = func(self, *args, **kwargs)
        elapsed = time.time() - start
        
        # Update status bar with timing
        if hasattr(self, 'timing_label'):
            self.timing_label.setText(f"Query time: {elapsed:.2f}s")
        
        return result
    return wrapper

def ensure_connection(func):
    """Decorator to handle connection drops"""
    @wraps(func)
    def wrapper(self, *args, **kwargs):
        try:
            return func(self, *args, **kwargs)
        except pyodbc.Error as e:
            if 'Communication link failure' in str(e) or 'disconnected' in str(e).lower():
                reply = QMessageBox.question(
                    self, "Connection Lost",
                    "Database connection was lost. Reconnect?",
                    QMessageBox.Yes | QMessageBox.No
                )
                if reply == QMessageBox.Yes:
                    self.connect_to_server()
                    return func(self, *args, **kwargs)
            raise
    return wrapper

class SessionManager:
    """Manage session history and favorites"""
    def __init__(self, config_file="bolt_manager_config.json"):
        self.config_file = config_file
        self.load_config()
    
    def load_config(self):
        try:
            with open(self.config_file, 'r') as f:
                self.config = json.load(f)
        except:
            self.config = {
                'recent_tables': [],
                'favorite_filters': {},
                'last_session': None,
                'last_database': None,
                'custom_bolts': []  # Track user-created bolts
            }
    
    def save_config(self):
        """Save configuration to file"""
        try:
            with open(self.config_file, 'w') as f:
                json.dump(self.config, f, indent=2)
        except Exception as e:
            print(f"Error saving config: {e}")
    
    def add_recent_table(self, table_name):
        """Track recently accessed tables"""
        self.config['recent_tables'] = [
            table_name
        ] + [t for t in self.config['recent_tables'] if t != table_name][:9]
        self.save_config()
    
    def save_filter_preset(self, name, table, filters, column_filters):
        """Save a filter configuration as a preset"""
        self.config['favorite_filters'][name] = {
            'table': table,
            'global_filter': filters,
            'column_filters': column_filters,
            'created': datetime.now().isoformat()
        }
        self.save_config()
    
    def get_filter_presets(self, table=None):
        """Get saved filter presets"""
        if table:
            return {k: v for k, v in self.config['favorite_filters'].items() 
                    if v.get('table') == table}
        return self.config['favorite_filters']
    
    def add_custom_bolt(self, bolt_info):
        """Track custom bolt creation"""
        self.config['custom_bolts'].append({
            'name': bolt_info['name'],
            'created': datetime.now().isoformat(),
            'standard': bolt_info.get('standard', ''),
            'diameter': bolt_info.get('diameter', 0)
        })
        self.save_config()

class AdvancedSearchDialog(QDialog):
    """Dialog for advanced search with multiple conditions"""
    def __init__(self, columns, parent=None):
        super().__init__(parent)
        self.columns = columns
        self.conditions = []
        self.condition_widgets = []
        self.init_ui()
    
    def init_ui(self):
        self.setWindowTitle("Advanced Search")
        self.resize(500, 400)
        layout = QVBoxLayout()
        
        # Instructions
        layout.addWidget(QLabel("Add multiple search conditions:"))
        
        # Conditions area with scroll
        scroll = QScrollArea()
        scroll_widget = QWidget()
        self.conditions_layout = QVBoxLayout(scroll_widget)
        scroll.setWidget(scroll_widget)
        scroll.setWidgetResizable(True)
        layout.addWidget(scroll)
        
        # Add condition button
        add_btn = QPushButton("➕ Add Condition")
        add_btn.clicked.connect(self.add_condition)
        layout.addWidget(add_btn)
        
        # Buttons
        btn_layout = QHBoxLayout()
        search_btn = QPushButton("Search")
        search_btn.clicked.connect(self.accept)
        cancel_btn = QPushButton("Cancel")
        cancel_btn.clicked.connect(self.reject)
        
        btn_layout.addWidget(search_btn)
        btn_layout.addWidget(cancel_btn)
        layout.addLayout(btn_layout)
        
        self.setLayout(layout)
        
        # Add first condition by default
        self.add_condition()
    
    def add_condition(self):
        """Add a new search condition"""
        condition_frame = QWidget()
        layout = QHBoxLayout(condition_frame)
        
        # Column dropdown
        col_combo = QComboBox()
        col_combo.addItems(self.columns)
        layout.addWidget(col_combo)
        
        # Operator dropdown
        op_combo = QComboBox()
        op_combo.addItems(['contains', 'equals', 'starts with', 'ends with', 'not contains'])
        layout.addWidget(op_combo)
        
        # Value input
        value_input = QLineEdit()
        value_input.setPlaceholderText("Enter search value...")
        layout.addWidget(value_input)
        
        # Remove button
        remove_btn = QPushButton("❌")
        remove_btn.setMaximumWidth(30)
        remove_btn.clicked.connect(lambda: self.remove_condition(condition_frame))
        layout.addWidget(remove_btn)
        
        self.conditions_layout.addWidget(condition_frame)
        self.condition_widgets.append((condition_frame, col_combo, op_combo, value_input))
    
    def remove_condition(self, condition_frame):
        """Remove a search condition"""
        for i, (frame, _, _, _) in enumerate(self.condition_widgets):
            if frame == condition_frame:
                self.condition_widgets.pop(i)
                condition_frame.deleteLater()
                break
    
    def get_conditions(self):
        """Get all conditions as a list"""
        conditions = []
        for _, col_combo, op_combo, value_input in self.condition_widgets:
            if value_input.text().strip():
                conditions.append({
                    'column': col_combo.currentText(),
                    'operator': op_combo.currentText(),
                    'value': value_input.text().strip()
                })
        return conditions

class ScrollableFilterDialog(QDialog):
    """Custom dialog with scrollable filter options"""
    filter_selected = pyqtSignal(str)
    
    def __init__(self, column_name, unique_values, current_filter="", parent=None):
        super().__init__(parent)
        self.column_name = column_name
        self.unique_values = unique_values
        self.current_filter = current_filter
        self.filtered_values = unique_values.copy()
        
        self.setWindowTitle(f"Filter: {column_name}")
        self.setModal(True)
        self.resize(300, 400)
        
        self.init_ui()
        self.filter_list()
    
    def init_ui(self):
        layout = QVBoxLayout()
        
        # Search box for filtering options
        search_layout = QHBoxLayout()
        search_layout.addWidget(QLabel("Search:"))
        self.search_box = QLineEdit()
        self.search_box.setPlaceholderText("Type to filter options...")
        self.search_box.textChanged.connect(self.filter_list)
        search_layout.addWidget(self.search_box)
        layout.addLayout(search_layout)
        
        # List widget for filter options
        self.filter_list_widget = QListWidget()
        self.filter_list_widget.itemDoubleClicked.connect(self.on_item_selected)
        layout.addWidget(self.filter_list_widget)
        
        # Buttons
        button_layout = QHBoxLayout()
        
        self.clear_button = QPushButton("All (Clear Filter)")
        self.clear_button.clicked.connect(lambda: self.select_filter(""))
        
        self.ok_button = QPushButton("Apply")
        self.ok_button.clicked.connect(self.apply_selected_filter)
        
        self.cancel_button = QPushButton("Cancel")
        self.cancel_button.clicked.connect(self.reject)
        
        button_layout.addWidget(self.clear_button)
        button_layout.addStretch()
        button_layout.addWidget(self.ok_button)
        button_layout.addWidget(self.cancel_button)
        
        layout.addLayout(button_layout)
        self.setLayout(layout)
    
    def filter_list(self):
        """Filter the list based on search text"""
        search_text = self.search_box.text().lower()
        self.filtered_values = []
        
        for value in self.unique_values:
            if search_text in str(value).lower():
                self.filtered_values.append(value)
        
        # Update list widget
        self.filter_list_widget.clear()
        for value in self.filtered_values:
            item = QListWidgetItem(str(value))
            item.setData(Qt.UserRole, value)
            
            # Highlight current filter
            if str(value) == str(self.current_filter):
                item.setBackground(item.listWidget().palette().highlight())
                item.setForeground(item.listWidget().palette().highlightedText())
            
            self.filter_list_widget.addItem(item)
    
    def on_item_selected(self, item):
        """Handle double-click on item"""
        value = item.data(Qt.UserRole)
        self.select_filter(str(value))
    
    def apply_selected_filter(self):
        """Apply the currently selected filter"""
        current_item = self.filter_list_widget.currentItem()
        if current_item:
            value = current_item.data(Qt.UserRole)
            self.select_filter(str(value))
        else:
            self.reject()
    
    def select_filter(self, filter_value):
        """Emit the selected filter and close dialog"""
        self.filter_selected.emit(filter_value)
        self.accept()


class ScrollableMenu(QMenu):
    """Custom QMenu with scrollable content"""
    
    def __init__(self, max_visible_items=15, parent=None):
        super().__init__(parent)
        self.max_visible_items = max_visible_items
        self.scroll_area = None
        self.content_widget = None
        
    def add_scrollable_actions(self, actions_data):
        """Add actions that will be scrollable if they exceed max_visible_items
        
        Args:
            actions_data: List of tuples (text, callback) or (text, callback, data)
        """
        if len(actions_data) <= self.max_visible_items:
            # Use regular menu if items fit
            for action_data in actions_data:
                if len(action_data) == 2:
                    text, callback = action_data
                    action = QAction(text, self)
                    action.triggered.connect(callback)
                else:
                    text, callback, data = action_data
                    action = QAction(text, self)
                    action.triggered.connect(lambda checked, d=data: callback(d))
                self.addAction(action)
        else:
            # Create scrollable widget
            self.scroll_area = QScrollArea()
            self.content_widget = QWidget()
            layout = QVBoxLayout(self.content_widget)
            layout.setContentsMargins(5, 5, 5, 5)
            layout.setSpacing(2)
            
            # Add buttons for each action
            for action_data in actions_data:
                if len(action_data) == 2:
                    text, callback = action_data
                    button = QPushButton(text)
                    button.clicked.connect(lambda checked, cb=callback: self.handle_button_click(cb))
                else:
                    text, callback, data = action_data
                    button = QPushButton(text)
                    button.clicked.connect(lambda checked, cb=callback, d=data: self.handle_button_click(cb, d))
                
                button.setFlat(True)
                button.setStyleSheet("QPushButton { text-align: left; padding: 4px 8px; }")
                layout.addWidget(button)
            
            self.scroll_area.setWidget(self.content_widget)
            self.scroll_area.setWidgetResizable(True)
            self.scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
            self.scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
            
            # Set size constraints
            self.scroll_area.setMinimumHeight(min(300, len(actions_data) * 30))
            self.scroll_area.setMaximumHeight(400)
            self.scroll_area.setMinimumWidth(200)
            
            # Add scroll area to menu
            action = self.addAction("")
            self.setDefaultAction(action)
            action.setEnabled(False)
            
            # Use a widget action to embed the scroll area
            widget_action = QWidgetAction(self)
            widget_action.setDefaultWidget(self.scroll_area)
            self.addAction(widget_action)
    
    def handle_button_click(self, callback, data=None):
        """Handle button click in scrollable menu"""
        self.close()
        if data is not None:
            callback(data)
        else:
            callback()


class TableLoader(QThread):
    """Background thread for loading table data"""
    tables_loaded = pyqtSignal(list)
    error_occurred = pyqtSignal(str)
    
    def __init__(self, cursor):
        super().__init__()
        self.cursor = cursor
    
    def run(self):
        try:
            self.cursor.execute("SELECT TABLE_NAME FROM INFORMATION_SCHEMA.TABLES")
            all_tables = [row[0] for row in self.cursor.fetchall()]
            filtered = sorted([t for t in all_tables if t in FASTENER_TABLES])
            self.tables_loaded.emit(filtered)
        except Exception as e:
            self.error_occurred.emit(str(e))

class BoltManager(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("AdvSteel FastenSuite - Schema-Aware Edition")
        self.connection = None
        self.cursor = None
        self.current_table = None
        self.tables = []
        self.page = 0
        self.rows_per_page = 25
        self.convert_to_inches = False
        self.total_filtered_rows = 0
        self.sort_column = None
        self.sort_order = "ASC"
        self.column_filters = {}  # {column_name: filter_value}
        self.advanced_conditions = []  # For advanced search
        
        # Session manager
        self.session_manager = SessionManager()
        
        # Register cleanup on exit
        atexit.register(self.cleanup)
        
        self.init_ui()
        self.setup_shortcuts()

    def init_ui(self):
        self.layout = QVBoxLayout()

        # Add toolbar
        self.toolbar = self.create_toolbar()
        self.layout.addWidget(self.toolbar)

        # Create tab widget for main interface
        self.tabs = QTabWidget()
        
        # Tab 1: Table Browser
        self.browser_tab = self.create_browser_tab()
        self.tabs.addTab(self.browser_tab, "Table Browser")
        
        # Tab 2: Bolt Creation
        self.creation_tab = self.create_creation_tab()
        self.tabs.addTab(self.creation_tab, "Bolt Creation")
        
        # Tab 3: Schema Validation
        self.validation_tab = self.create_validation_tab()
        self.tabs.addTab(self.validation_tab, "Schema Validation")
        
        self.layout.addWidget(self.tabs)
        
        # Status bar
        self.status_bar = self.create_status_bar()
        self.layout.addWidget(self.status_bar)

        self.setLayout(self.layout)

    def create_browser_tab(self):
        """Create the table browser tab"""
        widget = QWidget()
        layout = QVBoxLayout()

        # Connection UI
        conn_group = QGroupBox("Database Connection")
        conn_layout = QVBoxLayout()
        
        self.status_label = QLabel("Not connected")
        self.connect_button = QPushButton("Connect to SQL Server")
        self.disconnect_button = QPushButton("Disconnect")
        self.disconnect_button.setEnabled(False)
        self.connect_button.clicked.connect(self.connect_to_server)
        self.disconnect_button.clicked.connect(self.disconnect_from_server)

        conn_layout.addWidget(self.status_label)
        conn_layout.addWidget(self.connect_button)
        conn_layout.addWidget(self.disconnect_button)

        # DB dropdown
        self.db_dropdown = QComboBox()
        default_path = Config.get_db_path()
        self.db_dropdown.addItem(default_path)
        
        # Add last used database if different
        last_db = self.session_manager.config.get('last_database')
        if last_db and last_db != default_path and Path(last_db).exists():
            self.db_dropdown.addItem(last_db)
        
        conn_layout.addWidget(QLabel("Database:"))
        conn_layout.addWidget(self.db_dropdown)
        conn_group.setLayout(conn_layout)
        layout.addWidget(conn_group)

        # Table list with recent tables highlighted
        tables_group = QGroupBox("Tables")
        tables_layout = QVBoxLayout()
        
        self.table_list = QListWidget()
        self.load_table_button = QPushButton("Load Tables")
        self.load_table_button.clicked.connect(self.load_tables)
        self.load_table_button.setEnabled(False)
        self.table_list.itemClicked.connect(self.load_table_data)
        tables_layout.addWidget(self.table_list)
        tables_layout.addWidget(self.load_table_button)
        
        # Add table relationship info
        self.table_info_label = QLabel("")
        self.table_info_label.setWordWrap(True)
        tables_layout.addWidget(self.table_info_label)
        
        tables_group.setLayout(tables_layout)
        layout.addWidget(tables_group)

        # Progress bar for loading operations
        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        layout.addWidget(self.progress_bar)

        # Filter box
        self.filter_box = QLineEdit()
        self.filter_box.setPlaceholderText("Filter by keyword (any column)... Press Ctrl+F to focus")
        self.filter_box.textChanged.connect(self.apply_filter)
        self.filter_box.setEnabled(False)
        layout.addWidget(self.filter_box)

        # Unit toggle
        self.unit_toggle = QCheckBox("Display in Inches")
        self.unit_toggle.stateChanged.connect(self.toggle_units)
        self.unit_toggle.setEnabled(False)
        layout.addWidget(self.unit_toggle)

        # Table view with sortable headers
        self.data_table = QTableWidget()
        self.data_table.setSortingEnabled(False)  # We'll handle sorting manually
        self.data_table.horizontalHeader().setSectionsClickable(True)
        self.data_table.horizontalHeader().sectionClicked.connect(self.on_header_clicked)
        self.data_table.horizontalHeader().setContextMenuPolicy(Qt.CustomContextMenu)
        self.data_table.horizontalHeader().customContextMenuRequested.connect(self.show_column_filter_menu)
        
        # Enable row selection for bulk operations
        self.data_table.setSelectionBehavior(QTableWidget.SelectRows)
        self.data_table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.data_table.customContextMenuRequested.connect(self.show_row_context_menu)
        
        layout.addWidget(QLabel("Table Data:"))
        layout.addWidget(self.data_table)

        # Pagination with row count info
        self.pagination_layout = QHBoxLayout()
        self.prev_button = QPushButton("⬅ Prev 25")
        self.next_button = QPushButton("Next 25 ➡")
        self.page_info_label = QLabel("No data loaded")
        
        self.prev_button.clicked.connect(lambda: self.change_page(-1))
        self.next_button.clicked.connect(lambda: self.change_page(1))
        self.prev_button.setEnabled(False)
        self.next_button.setEnabled(False)
        
        self.pagination_layout.addWidget(self.prev_button)
        self.pagination_layout.addWidget(self.page_info_label)
        self.pagination_layout.addWidget(self.next_button)
        layout.addLayout(self.pagination_layout)

        widget.setLayout(layout)
        return widget
        
    def create_creation_tab(self):
        """Create the bolt creation tab"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        # Connection required message
        self.creation_message = QLabel("Connect to database to enable bolt creation tools.")
        layout.addWidget(self.creation_message)
        
        # Create bolt button
        self.create_bolt_btn = QPushButton("Create New Bolt Assembly")
        self.create_bolt_btn.setEnabled(False)
        self.create_bolt_btn.clicked.connect(self.show_bolt_creation_wizard)
        layout.addWidget(self.create_bolt_btn)
        
        # Quick actions
        quick_group = QGroupBox("Quick Actions")
        quick_layout = QVBoxLayout()
        
        self.clone_bolt_btn = QPushButton("Clone Existing Bolt")
        self.clone_bolt_btn.setEnabled(False)
        self.clone_bolt_btn.clicked.connect(self.clone_existing_bolt)
        quick_layout.addWidget(self.clone_bolt_btn)
        
        self.add_length_btn = QPushButton("Add Length to Existing Bolt")
        self.add_length_btn.setEnabled(False)
        self.add_length_btn.clicked.connect(self.add_bolt_length)
        quick_layout.addWidget(self.add_length_btn)
        
        quick_group.setLayout(quick_layout)
        layout.addWidget(quick_group)
        
        # Recent custom bolts
        recent_group = QGroupBox("Recent Custom Bolts")
        recent_layout = QVBoxLayout()
        
        self.recent_bolts_list = QListWidget()
        recent_layout.addWidget(self.recent_bolts_list)
        
        recent_group.setLayout(recent_layout)
        layout.addWidget(recent_group)
        
        layout.addStretch()
        widget.setLayout(layout)
        return widget
        
    def create_validation_tab(self):
        """Create the schema validation tab"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        # Connection required message
        self.validation_message = QLabel("Connect to database to enable validation tools.")
        layout.addWidget(self.validation_message)
        
        # Validation widget placeholder
        self.validation_widget = None
        self.validation_container = QVBoxLayout()
        layout.addLayout(self.validation_container)
        
        layout.addStretch()
        widget.setLayout(layout)
        return widget
        # bolt_manager_schema_aware.py

import sys
import os
import atexit
import pyodbc
import json
import csv
import time
from pathlib import Path
from datetime import datetime
from functools import wraps
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Any
from PyQt5.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QLabel, QPushButton, QComboBox,
    QListWidget, QTableWidget, QTableWidgetItem, QHBoxLayout, QLineEdit, 
    QCheckBox, QMessageBox, QProgressBar, QHeaderView, QMenu, QAction,
    QScrollArea, QDialog, QListWidgetItem, QWidgetAction, QToolBar,
    QStatusBar, QFileDialog, QShortcut, QGroupBox, QSpinBox, QDoubleSpinBox,
    QTextEdit, QTabWidget, QFormLayout, QDialogButtonBox
)
from PyQt5.QtCore import Qt, QThread, pyqtSignal, QTimer
from PyQt5.QtGui import QKeySequence, QColor, QFont

# Configuration class for better path management
class Config:
    @staticmethod
    def get_db_path():
        """Get database path with fallback options"""
        # Allow environment variable override
        custom_path = os.environ.get('ADVSTEEL_DB_PATH')
        if custom_path and Path(custom_path).exists():
            return custom_path
        
        # Default path with year flexibility
        base_path = Path(r'C:\PROGRAMDATA\AUTODESK\ADVANCE STEEL')
        for year in range(2025, 2020, -1):  # Check recent years
            db_path = base_path / str(year) / 'USA/STEEL/DATA/ASTORBASE.MDF'
            if db_path.exists():
                return str(db_path)
        
        # Fallback to hardcoded path
        return r'C:\PROGRAMDATA\AUTODESK\ADVANCE STEEL 2025\USA\STEEL\DATA\ASTORBASE.MDF'

DB_CONFIG = {
    'server': r'(LocalDB)\ADVANCESTEEL2025',
    'trusted_connection': 'yes',
    'driver': 'ODBC Driver 17 for SQL Server',
    'database': Config.get_db_path()
}

# Configuration for unit conversion
UNIT_CONVERT = {
    'Diameter': True, 
    'Length': True, 
    'HeadHeight': True,
    'Width': True,
    'Height': True,
    'Thickness': True,
    'HeadDiameter': True,
    'NutThickness': True,
    'WasherThickness': True,
    'WasherOuterDia': True,
    'GripMin': True,
    'GripMax': True
}
MM_TO_INCH = 25.4

# Known fastener tables with their relationships
FASTENER_TABLES = {
    'BoltsCoating', 'BoltsDiameters', 'Screw', 'SetBolts', 'SetBoltsType', 'SetOfBolts', 'Standard',
    'BoltsDistances', 'BoltDefinition', 'TappingHole', 'Sources', 'Sets', 'SetNutsBolts', 'ScrewNew',
    'Authors', 'StrengthClass', 'AutoLength', 'StandardNuts'
}

# Critical table relationships for bolt creation
BOLT_SCHEMA = {
    'BoltDefinition': {
        'foreign_keys': {
            'StandardId': 'Standard',
            'StrengthClassId': 'StrengthClass',
            'AuthorId': 'Authors'
        },
        'required_fields': ['Name', 'StandardId', 'Diameter', 'StrengthClassId', 'AuthorId'],
        'description': 'Base bolt type definitions'
    },
    'SetBolts': {
        'foreign_keys': {
            'BoltDefId': 'BoltDefinition'
        },
        'required_fields': ['BoltDefId', 'Length', 'Weight', 'PartName'],
        'description': 'Individual bolt lengths'
    },
    'SetOfBolts': {
        'foreign_keys': {
            'BoltDefId': 'BoltDefinition',
            'SetId': 'Sets'
        },
        'required_fields': ['BoltDefId', 'SetId'],
        'description': 'Links bolts to assembly sets'
    },
    'SetNutsBolts': {
        'foreign_keys': {
            'StandardId': 'Standard',
            'SetId': 'Sets'
        },
        'required_fields': ['StandardId', 'SetId', 'Diameter', 'NutThickness', 'WasherThickness'],
        'description': 'Nut and washer dimensions'
    },
    'AutoLength': {
        'foreign_keys': {
            'BoltDefId': 'BoltDefinition'
        },
        'required_fields': ['BoltDefId', 'GripMin', 'GripMax', 'Length'],
        'description': 'Automatic length selection rules'
    }
}

@dataclass
class BoltData:
    """Data class for bolt information"""
    name: str
    standard_id: int
    diameter: float
    strength_class_id: int
    author_id: int
    head_diameter: float = None
    head_height: float = None
    thread_type: str = 'metric_coarse'
    lengths: List[Tuple[float, float, str]] = None  # (length, weight, part_name)
    assembly_sets: List[int] = None  # Set IDs
    
class DatabaseTransaction:
    """Context manager for database transactions"""
    def __init__(self, connection):
        self.connection = connection
        self.cursor = None
        
    def __enter__(self):
        self.cursor = self.connection.cursor()
        self.connection.commit()  # Ensure clean state
        return self.cursor
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self.connection.commit()
        else:
            self.connection.rollback()
            print(f"Transaction rolled back due to: {exc_val}")
        if self.cursor:
            self.cursor.close()

class BoltCreationWizard(QDialog):
    """Wizard for creating new bolts with proper schema compliance"""
    
    def __init__(self, cursor, parent=None):
        super().__init__(parent)
        self.cursor = cursor
        self.bolt_data = None
        self.setWindowTitle("Create New Bolt Assembly")
        self.resize(800, 600)
        self.init_ui()
        self.load_reference_data()
        
    def init_ui(self):
        layout = QVBoxLayout()
        
        # Tab widget for steps
        self.tabs = QTabWidget()
        
        # Step 1: Basic Properties
        self.basic_tab = self.create_basic_tab()
        self.tabs.addTab(self.basic_tab, "1. Basic Properties")
        
        # Step 2: Lengths
        self.lengths_tab = self.create_lengths_tab()
        self.tabs.addTab(self.lengths_tab, "2. Bolt Lengths")
        
        # Step 3: Assembly Sets
        self.assembly_tab = self.create_assembly_tab()
        self.tabs.addTab(self.assembly_tab, "3. Assembly Sets")
        
        # Step 4: Nut/Washer Data
        self.nut_washer_tab = self.create_nut_washer_tab()
        self.tabs.addTab(self.nut_washer_tab, "4. Nut/Washer Data")
        
        # Step 5: Auto Length Rules
        self.auto_length_tab = self.create_auto_length_tab()
        self.tabs.addTab(self.auto_length_tab, "5. Auto Length (Optional)")
        
        # Step 6: Preview
        self.preview_tab = self.create_preview_tab()
        self.tabs.addTab(self.preview_tab, "6. Preview & Create")
        
        layout.addWidget(self.tabs)
        
        # Buttons
        button_box = QDialogButtonBox(
            QDialogButtonBox.Ok | QDialogButtonBox.Cancel
        )
        button_box.accepted.connect(self.create_bolt)
        button_box.rejected.connect(self.reject)
        
        layout.addWidget(button_box)
        self.setLayout(layout)
        
    def create_basic_tab(self):
        """Create tab for basic bolt properties"""
        widget = QWidget()
        layout = QFormLayout()
        
        # Name
        self.name_input = QLineEdit()
        self.name_input.setPlaceholderText("e.g., Bolt M16-70 DIN 6914")
        layout.addRow("Bolt Name:", self.name_input)
        
        # Standard
        self.standard_combo = QComboBox()
        layout.addRow("Standard:", self.standard_combo)
        
        # Diameter
        self.diameter_input = QDoubleSpinBox()
        self.diameter_input.setRange(1.0, 100.0)
        self.diameter_input.setSuffix(" mm")
        self.diameter_input.setValue(16.0)
        layout.addRow("Diameter:", self.diameter_input)
        
        # Strength Class
        self.strength_combo = QComboBox()
        layout.addRow("Strength Class:", self.strength_combo)
        
        # Author
        self.author_combo = QComboBox()
        layout.addRow("Author:", self.author_combo)
        
        # Head dimensions
        group = QGroupBox("Head Dimensions")
        head_layout = QFormLayout()
        
        self.head_diameter_input = QDoubleSpinBox()
        self.head_diameter_input.setRange(1.0, 200.0)
        self.head_diameter_input.setSuffix(" mm")
        self.head_diameter_input.setValue(24.0)
        head_layout.addRow("Head Diameter/Width:", self.head_diameter_input)
        
        self.head_height_input = QDoubleSpinBox()
        self.head_height_input.setRange(1.0, 100.0)
        self.head_height_input.setSuffix(" mm")
        self.head_height_input.setValue(10.0)
        head_layout.addRow("Head Height:", self.head_height_input)
        
        group.setLayout(head_layout)
        layout.addRow(group)
        
        widget.setLayout(layout)
        return widget
        
    def create_lengths_tab(self):
        """Create tab for bolt lengths"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        # Instructions
        layout.addWidget(QLabel("Add bolt lengths:"))
        
        # Length input
        input_layout = QHBoxLayout()
        
        self.length_input = QDoubleSpinBox()
        self.length_input.setRange(10.0, 1000.0)
        self.length_input.setSuffix(" mm")
        self.length_input.setValue(70.0)
        input_layout.addWidget(QLabel("Length:"))
        input_layout.addWidget(self.length_input)
        
        self.weight_input = QDoubleSpinBox()
        self.weight_input.setRange(0.001, 10.0)
        self.weight_input.setSuffix(" kg")
        self.weight_input.setDecimals(3)
        self.weight_input.setValue(0.138)
        input_layout.addWidget(QLabel("Weight:"))
        input_layout.addWidget(self.weight_input)
        
        add_btn = QPushButton("Add Length")
        add_btn.clicked.connect(self.add_length)
        input_layout.addWidget(add_btn)
        
        layout.addLayout(input_layout)
        
        # Length list
        self.lengths_table = QTableWidget()
        self.lengths_table.setColumnCount(3)
        self.lengths_table.setHorizontalHeaderLabels(["Length (mm)", "Weight (kg)", "Part Name"])
        layout.addWidget(self.lengths_table)
        
        # Bulk add button
        bulk_btn = QPushButton("Bulk Add Standard Lengths...")
        bulk_btn.clicked.connect(self.bulk_add_lengths)
        layout.addWidget(bulk_btn)
        
        widget.setLayout(layout)
        return widget
        
    def create_assembly_tab(self):
        """Create tab for assembly sets"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        layout.addWidget(QLabel("Select allowed assembly sets:"))
        
        # Assembly set list
        self.assembly_list = QListWidget()
        self.assembly_list.setSelectionMode(QListWidget.MultiSelection)
        layout.addWidget(self.assembly_list)
        
        widget.setLayout(layout)
        return widget
        
    def create_nut_washer_tab(self):
        """Create tab for nut/washer data"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        layout.addWidget(QLabel("Verify nut and washer dimensions:"))
        
        # Input for current diameter
        check_layout = QHBoxLayout()
        check_btn = QPushButton("Check Existing Data")
        check_btn.clicked.connect(self.check_nut_washer_data)
        check_layout.addWidget(check_btn)
        layout.addLayout(check_layout)
        
        # Data display
        self.nut_washer_text = QTextEdit()
        self.nut_washer_text.setReadOnly(True)
        layout.addWidget(self.nut_washer_text)
        
        # Manual entry section
        group = QGroupBox("Add Missing Data")
        form_layout = QFormLayout()
        
        self.nut_thickness_input = QDoubleSpinBox()
        self.nut_thickness_input.setRange(1.0, 100.0)
        self.nut_thickness_input.setSuffix(" mm")
        form_layout.addRow("Nut Thickness:", self.nut_thickness_input)
        
        self.nut_width_input = QDoubleSpinBox()
        self.nut_width_input.setRange(1.0, 200.0)
        self.nut_width_input.setSuffix(" mm")
        form_layout.addRow("Nut Width AF:", self.nut_width_input)
        
        self.washer_thickness_input = QDoubleSpinBox()
        self.washer_thickness_input.setRange(0.5, 20.0)
        self.washer_thickness_input.setSuffix(" mm")
        form_layout.addRow("Washer Thickness:", self.washer_thickness_input)
        
        self.washer_diameter_input = QDoubleSpinBox()
        self.washer_diameter_input.setRange(1.0, 200.0)
        self.washer_diameter_input.setSuffix(" mm")
        form_layout.addRow("Washer Outer Dia:", self.washer_diameter_input)
        
        group.setLayout(form_layout)
        layout.addWidget(group)
        
        widget.setLayout(layout)
        return widget
        
    def create_auto_length_tab(self):
        """Create tab for auto length rules"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        layout.addWidget(QLabel("Optional: Define automatic length selection rules"))
        
        # Enable checkbox
        self.enable_auto_length = QCheckBox("Enable automatic length selection")
        layout.addWidget(self.enable_auto_length)
        
        # Auto-generate button
        generate_btn = QPushButton("Generate Standard Rules")
        generate_btn.clicked.connect(self.generate_auto_length_rules)
        layout.addWidget(generate_btn)
        
        # Rules table
        self.auto_length_table = QTableWidget()
        self.auto_length_table.setColumnCount(3)
        self.auto_length_table.setHorizontalHeaderLabels(["Grip Min", "Grip Max", "Length"])
        layout.addWidget(self.auto_length_table)
        
        widget.setLayout(layout)
        return widget
        
    def create_preview_tab(self):
        """Create preview tab"""
        widget = QWidget()
        layout = QVBoxLayout()
        
        layout.addWidget(QLabel("Review bolt data before creation:"))
        
        # Preview button
        preview_btn = QPushButton("Generate Preview")
        preview_btn.clicked.connect(self.generate_preview)
        layout.addWidget(preview_btn)
        
        # Preview text
        self.preview_text = QTextEdit()
        self.preview_text.setReadOnly(True)
        layout.addWidget(self.preview_text)
        
        # SQL preview
        self.sql_preview = QTextEdit()
        self.sql_preview.setReadOnly(True)
        self.sql_preview.setMaximumHeight(200)
        layout.addWidget(QLabel("SQL Commands to be executed:"))
        layout.addWidget(self.sql_preview)
        
        widget.setLayout(layout)
        return widget
        
    def load_reference_data(self):
        """Load reference data for dropdowns"""
        try:
            # Load standards
            self.cursor.execute("SELECT ID, Name FROM Standard ORDER BY Name")
            standards = self.cursor.fetchall()
            for std_id, name in standards:
                self.standard_combo.addItem(name, std_id)
            
            # Load strength classes
            self.cursor.execute("SELECT ID, Name FROM StrengthClass ORDER BY Name")
            strengths = self.cursor.fetchall()
            for str_id, name in strengths:
                self.strength_combo.addItem(name, str_id)
            
            # Load authors
            self.cursor.execute("SELECT ID, Name FROM Authors ORDER BY Name")
            authors = self.cursor.fetchall()
            for auth_id, name in authors:
                self.author_combo.addItem(name, auth_id)
            
            # Load assembly sets
            self.cursor.execute("SELECT ID, SetCode, Description FROM Sets ORDER BY SetCode")
            sets = self.cursor.fetchall()
            for set_id, code, desc in sets:
                item_text = f"{code} - {desc}" if desc else code
                item = QListWidgetItem(item_text)
                item.setData(Qt.UserRole, set_id)
                self.assembly_list.addItem(item)
            
        except Exception as e:
            QMessageBox.warning(self, "Load Error", f"Error loading reference data: {str(e)}")
            
    def add_length(self):
        """Add a bolt length to the table"""
        length = self.length_input.value()
        weight = self.weight_input.value()
        diameter = self.diameter_input.value()
        part_name = f"M{int(diameter)}x{int(length)}"
        
        row = self.lengths_table.rowCount()
        self.lengths_table.insertRow(row)
        self.lengths_table.setItem(row, 0, QTableWidgetItem(str(length)))
        self.lengths_table.setItem(row, 1, QTableWidgetItem(str(weight)))
        self.lengths_table.setItem(row, 2, QTableWidgetItem(part_name))
        
    def bulk_add_lengths(self):
        """Bulk add standard lengths"""
        dialog = QDialog(self)
        dialog.setWindowTitle("Bulk Add Lengths")
        layout = QVBoxLayout()
        
        # Range inputs
        form_layout = QFormLayout()
        
        start_input = QSpinBox()
        start_input.setRange(10, 1000)
        start_input.setValue(30)
        form_layout.addRow("Start Length (mm):", start_input)
        
        end_input = QSpinBox()
        end_input.setRange(10, 1000)
        end_input.setValue(200)
        form_layout.addRow("End Length (mm):", end_input)
        
        increment_input = QSpinBox()
        increment_input.setRange(5, 50)
        increment_input.setValue(10)
        form_layout.addRow("Increment (mm):", increment_input)
        
        layout.addLayout(form_layout)
        
        # Buttons
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        layout.addWidget(buttons)
        
        dialog.setLayout(layout)
        
        if dialog.exec_():
            # Generate lengths
            diameter = self.diameter_input.value()
            for length in range(start_input.value(), end_input.value() + 1, increment_input.value()):
                # Estimate weight (simplified formula)
                weight = round(length * diameter * diameter * 0.00000617, 3)
                part_name = f"M{int(diameter)}x{int(length)}"
                
                row = self.lengths_table.rowCount()
                self.lengths_table.insertRow(row)
                self.lengths_table.setItem(row, 0, QTableWidgetItem(str(length)))
                self.lengths_table.setItem(row, 1, QTableWidgetItem(str(weight)))
                self.lengths_table.setItem(row, 2, QTableWidgetItem(part_name))
                
    def check_nut_washer_data(self):
        """Check existing nut/washer data"""
        standard_id = self.standard_combo.currentData()
        diameter = self.diameter_input.value()
        
        # Get selected assembly sets
        selected_sets = []
        for i in range(self.assembly_list.count()):
            item = self.assembly_list.item(i)
            if item.isSelected():
                selected_sets.append((item.data(Qt.UserRole), item.text()))
        
        if not selected_sets:
            self.nut_washer_text.setText("Please select at least one assembly set first.")
            return
            
        report = []
        missing = []
        
        for set_id, set_name in selected_sets:
            query = """
                SELECT NutThickness, NutWidthAcrossFlats, WasherThickness, WasherOuterDia
                FROM SetNutsBolts
                WHERE StandardId = ? AND SetId = ? AND Diameter = ?
            """
            self.cursor.execute(query, (standard_id, set_id, diameter))
            result = self.cursor.fetchone()
            
            if result:
                report.append(f"✓ {set_name}:")
                report.append(f"  Nut: {result[0]}mm thick, {result[1]}mm AF")
                report.append(f"  Washer: {result[2]}mm thick, {result[3]}mm OD")
            else:
                report.append(f"✗ {set_name}: NO DATA FOUND")
                missing.append(set_id)
                
        self.nut_washer_text.setText("\n".join(report))
        
        if missing:
            QMessageBox.warning(self, "Missing Data", 
                              f"Missing nut/washer data for {len(missing)} assembly set(s). "
                              "Please add the data below.")
                              
    def generate_auto_length_rules(self):
        """Generate standard auto-length rules"""
        if self.lengths_table.rowCount() == 0:
            QMessageBox.warning(self, "No Lengths", "Please add bolt lengths first.")
            return
            
        # Get all lengths
        lengths = []
        for row in range(self.lengths_table.rowCount()):
            length = float(self.lengths_table.item(row, 0).text())
            lengths.append(length)
        lengths.sort()
        
        # Clear existing rules
        self.auto_length_table.setRowCount(0)
        
        # Generate rules (simplified algorithm)
        # Typically: bolt_length = grip + nut_height + 2-3 threads projection
        nut_height = self.nut_thickness_input.value() or 13.0  # Default for M16
        thread_projection = 3.0  # 3mm projection
        
        for length in lengths:
            max_grip = length - nut_height - thread_projection
            min_grip = 0 if self.auto_length_table.rowCount() == 0 else prev_max_grip + 0.1
            
            if max_grip > min_grip:
                row = self.auto_length_table.rowCount()
                self.auto_length_table.insertRow(row)
                self.auto_length_table.setItem(row, 0, QTableWidgetItem(f"{min_grip:.1f}"))
                self.auto_length_table.setItem(row, 1, QTableWidgetItem(f"{max_grip:.1f}"))
                self.auto_length_table.setItem(row, 2, QTableWidgetItem(str(length)))
                
                prev_max_grip = max_grip
                
    def generate_preview(self):
        """Generate preview of bolt data"""
        # Collect all data
        bolt_name = self.name_input.text()
        if not bolt_name:
            QMessageBox.warning(self, "Incomplete Data", "Please enter a bolt name.")
            return
            
        preview_lines = [
            "=== BOLT CREATION PREVIEW ===",
            f"Name: {bolt_name}",
            f"Standard: {self.standard_combo.currentText()}",
            f"Diameter: {self.diameter_input.value()} mm",
            f"Strength Class: {self.strength_combo.currentText()}",
            f"Author: {self.author_combo.currentText()}",
            f"Head Dimensions: {self.head_diameter_input.value()}mm x {self.head_height_input.value()}mm",
            "",
            f"Lengths: {self.lengths_table.rowCount()} entries",
        ]
        
        # Selected assembly sets
        selected_count = len([i for i in range(self.assembly_list.count()) 
                            if self.assembly_list.item(i).isSelected()])
        preview_lines.append(f"Assembly Sets: {selected_count} selected")
        
        # Auto length
        if self.enable_auto_length.isChecked():
            preview_lines.append(f"Auto Length Rules: {self.auto_length_table.rowCount()} rules")
        
        self.preview_text.setText("\n".join(preview_lines))
        
        # Generate SQL preview
        sql_lines = [
            "-- BoltDefinition insert",
            f"INSERT INTO BoltDefinition (Name, StandardId, Diameter, ...) VALUES ('{bolt_name}', ...)",
            "",
            f"-- SetBolts inserts ({self.lengths_table.rowCount()} rows)",
            "INSERT INTO SetBolts (BoltDefId, Length, Weight, PartName) VALUES ...",
            "",
            f"-- SetOfBolts inserts ({selected_count} rows)",
            "INSERT INTO SetOfBolts (BoltDefId, SetId) VALUES ...",
        ]
        
        self.sql_preview.setText("\n".join(sql_lines))
        
    def create_bolt(self):
        """Create the bolt with all related data"""
        # Validate data
        if not self.name_input.text():
            QMessageBox.warning(self, "Validation Error", "Bolt name is required.")
            return
            
        if self.lengths_table.rowCount() == 0:
            QMessageBox.warning(self, "Validation Error", "At least one bolt length is required.")
            return
            
        selected_sets = [i for i in range(self.assembly_list.count()) 
                        if self.assembly_list.item(i).isSelected()]
        if not selected_sets:
            QMessageBox.warning(self, "Validation Error", "At least one assembly set must be selected.")
            return
            
        # Collect all data
        self.bolt_data = BoltData(
            name=self.name_input.text(),
            standard_id=self.standard_combo.currentData(),
            diameter=self.diameter_input.value(),
            strength_class_id=self.strength_combo.currentData(),
            author_id=self.author_combo.currentData(),
            head_diameter=self.head_diameter_input.value(),
            head_height=self.head_height_input.value()
        )
        
        # Collect lengths
        self.bolt_data.lengths = []
        for row in range(self.lengths_table.rowCount()):
            length = float(self.lengths_table.item(row, 0).text())
            weight = float(self.lengths_table.item(row, 1).text())
            part_name = self.lengths_table.item(row, 2).text()
            self.bolt_data.lengths.append((length, weight, part_name))
            
        # Collect assembly sets
        self.bolt_data.assembly_sets = []
        for i in selected_sets:
            set_id = self.assembly_list.item(i).data(Qt.UserRole)
            self.bolt_data.assembly_sets.append(set_id)
            
        self.accept()

class SchemaValidationWidget(QWidget):
    """Widget for validating database schema and relationships"""
    
    def __init__(self, cursor, parent=None):
        super().__init__(parent)
        self.cursor = cursor
        self.init_ui()
        
    def init_ui(self):
        layout = QVBoxLayout()
        
        # Validation options
        layout.addWidget(QLabel("Schema Validation Tools:"))
        
        # Check buttons
        btn_layout = QVBoxLayout()
        
        check_orphans_btn = QPushButton("Check for Orphaned Records")
        check_orphans_btn.clicked.connect(self.check_orphaned_records)
        btn_layout.addWidget(check_orphans_btn)
        
        check_missing_btn = QPushButton("Check Missing SetNutsBolts Data")
        check_missing_btn.clicked.connect(self.check_missing_nut_data)
        btn_layout.addWidget(check_missing_btn)
        
        check_incomplete_btn = QPushButton("Check Incomplete Bolt Definitions")
        check_incomplete_btn.clicked.connect(self.check_incomplete_bolts)
        btn_layout.addWidget(check_incomplete_btn)
        
        validate_lengths_btn = QPushButton("Validate AutoLength Coverage")
        validate_lengths_btn.clicked.connect(self.validate_auto_length)
        btn_layout.addWidget(validate_lengths_btn)
        
        layout.addLayout(btn_layout)
        
        # Results display
        self.results_text = QTextEdit()
        self.results_text.setReadOnly(True)
        layout.addWidget(self.results_text)
        
        self.setLayout(layout)
        
    def check_orphaned_records(self):
        """Check for orphaned records across tables"""
        results = ["=== ORPHANED RECORDS CHECK ===\n"]
        
        checks = [
            ("SetBolts without BoltDefinition", 
             "SELECT COUNT(*) FROM SetBolts WHERE BoltDefId NOT IN (SELECT ID FROM BoltDefinition)"),
            ("SetOfBolts without BoltDefinition",
             "SELECT COUNT(*) FROM SetOfBolts WHERE BoltDefId NOT IN (SELECT ID FROM BoltDefinition)"),
            ("SetOfBolts without valid Set",
             "SELECT COUNT(*) FROM SetOfBolts WHERE SetId NOT IN (SELECT ID FROM Sets)"),
            ("AutoLength without BoltDefinition",
             "SELECT COUNT(*) FROM AutoLength WHERE BoltDefId NOT IN (SELECT ID FROM BoltDefinition)"),
            ("BoltDefinition without Standard",
             "SELECT COUNT(*) FROM BoltDefinition WHERE StandardId NOT IN (SELECT ID FROM Standard)"),
            ("BoltDefinition without StrengthClass",
             "SELECT COUNT(*) FROM BoltDefinition WHERE StrengthClassId NOT IN (SELECT ID FROM StrengthClass)"),
        ]
        
        total_orphans = 0
        for desc, query in checks:
            try:
                self.cursor.execute(query)
                count = self.cursor.fetchone()[0]
                total_orphans += count
                status = "✓" if count == 0 else "✗"
                results.append(f"{status} {desc}: {count}")
            except Exception as e:
                results.append(f"❌ {desc}: ERROR - {str(e)}")
                
        results.append(f"\nTotal orphaned records: {total_orphans}")
        self.results_text.setText("\n".join(results))
        
    def check_missing_nut_data(self):
        """Check for missing SetNutsBolts entries"""
        results = ["=== MISSING NUT/WASHER DATA CHECK ===\n"]
        
        query = """
            SELECT DISTINCT bd.StandardId, s.Name as StandardName, bd.Diameter, 
                   st.SetCode, COUNT(*) as BoltCount
            FROM BoltDefinition bd
            JOIN Standard s ON bd.StandardId = s.ID
            JOIN SetOfBolts sob ON sob.BoltDefId = bd.ID
            JOIN Sets st ON st.ID = sob.SetId
            LEFT JOIN SetNutsBolts snb ON snb.StandardId = bd.StandardId 
                AND snb.SetId = sob.SetId AND snb.Diameter = bd.Diameter
            WHERE snb.StandardId IS NULL
            GROUP BY bd.StandardId, s.Name, bd.Diameter, st.SetCode
            ORDER BY s.Name, bd.Diameter
        """
        
        try:
            self.cursor.execute(query)
            missing_data = self.cursor.fetchall()
            
            if not missing_data:
                results.append("✓ All bolt assemblies have nut/washer data defined!")
            else:
                results.append(f"✗ Found {len(missing_data)} missing nut/washer configurations:\n")
                for std_id, std_name, diameter, set_code, bolt_count in missing_data:
                    results.append(f"  - {std_name} Ø{diameter}mm with {set_code} ({bolt_count} bolts affected)")
                    
        except Exception as e:
            results.append(f"ERROR: {str(e)}")
            
        self.results_text.setText("\n".join(results))
        
    def check_incomplete_bolts(self):
        """Check for bolt definitions without required relationships"""
        results = ["=== INCOMPLETE BOLT DEFINITIONS CHECK ===\n"]
        
        # Bolts without any lengths
        query1 = """
            SELECT bd.ID, bd.Name 
            FROM BoltDefinition bd
            LEFT JOIN SetBolts sb ON sb.BoltDefId = bd.ID
            WHERE sb.BoltDefId IS NULL
        """
        
        # Bolts without assembly sets
        query2 = """
            SELECT bd.ID, bd.Name 
            FROM BoltDefinition bd
            LEFT JOIN SetOfBolts sob ON sob.BoltDefId = bd.ID
            WHERE sob.BoltDefId IS NULL
        """
        
        try:
            # Check for bolts without lengths
            self.cursor.execute(query1)
            no_lengths = self.cursor.fetchall()
            
            if no_lengths:
                results.append(f"✗ Bolts without any lengths ({len(no_lengths)}):")
                for bolt_id, name in no_lengths[:10]:  # Show first 10
                    results.append(f"  - ID {bolt_id}: {name}")
                if len(no_lengths) > 10:
                    results.append(f"  ... and {len(no_lengths) - 10} more")
            else:
                results.append("✓ All bolts have at least one length defined")
                
            results.append("")
            
            # Check for bolts without assembly sets
            self.cursor.execute(query2)
            no_sets = self.cursor.fetchall()
            
            if no_sets:
                results.append(f"✗ Bolts without assembly sets ({len(no_sets)}):")
                for bolt_id, name in no_sets[:10]:
                    results.append(f"  - ID {bolt_id}: {name}")
                if len(no_sets) > 10:
                    results.append(f"  ... and {len(no_sets) - 10} more")
            else:
                results.append("✓ All bolts have at least one assembly set")
                
        except Exception as e:
            results.append(f"ERROR: {str(e)}")
            
        self.results_text.setText("\n".join(results))
        
    def validate_auto_length(self):
        """Validate AutoLength coverage"""
        results = ["=== AUTO LENGTH VALIDATION ===\n"]
        
        query = """
            SELECT bd.Name, COUNT(DISTINCT sb.Length) as LengthCount,
                   COUNT(DISTINCT al.Length) as AutoLengthCount,
                   MIN(al.GripMin) as MinGrip, MAX(al.GripMax) as MaxGrip
            FROM BoltDefinition bd
            LEFT JOIN SetBolts sb ON sb.BoltDefId = bd.ID
            LEFT JOIN AutoLength al ON al.BoltDefId = bd.ID
            GROUP BY bd.ID, bd.Name
            HAVING COUNT(DISTINCT sb.Length) > 0
            ORDER BY bd.Name
        """
        
        try:
            self.cursor.execute(query)
            bolt_data = self.cursor.fetchall()
            
            no_auto = 0
            incomplete = 0
            
            for name, length_count, auto_count, min_grip, max_grip in bolt_data:
                if auto_count == 0:
                    no_auto += 1
                elif auto_count < length_count:
                    incomplete += 1
                    results.append(f"⚠ {name}: {auto_count}/{length_count} lengths covered")
                    
            results.insert(1, f"Total bolts: {len(bolt_data)}")
            results.insert(2, f"Bolts without AutoLength: {no_auto}")
            results.insert(3, f"Bolts with incomplete AutoLength: {incomplete}")
            results.insert(4, "")
            
        except Exception as e:
            results.append(f"ERROR: {str(e)}")
            
        self.results_text.setText("\n".join(results)
