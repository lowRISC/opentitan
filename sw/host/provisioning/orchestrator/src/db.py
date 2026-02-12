# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Module for interacting with a SQLite database."""

import sqlite3
import datetime
import json
from dataclasses import dataclass

import ot_dut


@dataclass
class DBConfig(object):
    db_path: str


class DB(object):
    """Class for interacting with a SQLite database."""

    def __init__(self, db_config: DBConfig):
        self.db_path = db_config.db_path
        self._conn = None

    def __del__(self):
        if self._conn:
            self._conn.close()

    def try_cursor(self):
        """Returns a cursor to the database."""
        if not self._conn:
            self._conn = sqlite3.connect(self.db_path)
        return self._conn.cursor()

    def commit(self):
        """Commits the connection to the database."""
        if not self._conn:
            raise RuntimeError("No connection to commit")
        self._conn.commit()


@dataclass
class DeviceRecord(object):
    """Class for holding data and routines for device records."""
    device_id: str
    sku: str
    provisioning_state: str
    timestamp: int
    rma_unlock_token: str
    dice_uds: str
    cp_json: str
    ft_json: str
    last_update: int

    @staticmethod
    def schema_list():
        schema = []
        type_map = {"str": "text", "int": "int"}
        for key, value in DeviceRecord.__annotations__.items():
            schema.append(f"{key} {type_map[value.__name__]}")
        return schema

    @staticmethod
    def table_name() -> str:
        return "device_records"

    def columns() -> [str]:
        return list(DeviceRecord.__annotations__.keys())

    @staticmethod
    def create_table_string(table_name: str) -> str:
        """Returns a string to create a table in the database.

        Args:
            table_name: The name of the table to create.
        Returns:
            A string to create a table in the database.
        """
        return f"CREATE TABLE IF NOT EXISTS {table_name} ({', '.join(DeviceRecord.schema_list())})"

    @staticmethod
    def create_table(db: DB):
        """Creates a table in the database.

        Args:
            db: The database object.
        """
        c = db.try_cursor()
        c.execute(DeviceRecord.create_table_string(DeviceRecord.table_name()))
        db.commit()

    @staticmethod
    def query(db: DB, device_id: str) -> 'DeviceRecord':
        """Queries the database for the record.

        Args:
            db: The database object.
        Returns:
            The record from the database.
        """
        c = db.try_cursor()
        c.execute(
            f"SELECT * FROM {DeviceRecord.table_name()} WHERE device_id=?",
            (device_id, ))
        record = c.fetchone()
        if record is None:
            return None
        return DeviceRecord(*record)

    @staticmethod
    def query_all(db: DB) -> ['DeviceRecord']:
        """Queries the database for all records.

        Args:
            db: The database object.
        Returns:
            All records from the database.
        """
        c = db.try_cursor()
        c.execute(f"SELECT * FROM {DeviceRecord.table_name()}")
        records = c.fetchall()
        return [DeviceRecord(*record) for record in records]

    @staticmethod
    def from_dut(dut: ot_dut.OtDut) -> 'DeviceRecord':
        """Creates a DeviceRecord object from a DUT object.

        Args:
            dut: The DUT object.
        Returns:
            A DeviceRecord object.
        """
        dice_uds = ""
        if "UDS" in dut.ft_data["certs"]:
            dice_uds = dut.ft_data["certs"]["UDS"]["bytes"]
        return DeviceRecord(
            device_id=dut.device_id.to_hexstr(),
            sku=str(dut.device_id.sku),
            provisioning_state=dut.ft_data["lc_state"]["mission_mode"],
            timestamp=0,
            rma_unlock_token=str(dut.ft_data["rma_unlock_token"]),
            dice_uds=str(dice_uds),
            cp_json=json.dumps(dut.cp_data),
            ft_json=json.dumps(dut.ft_data),
            last_update=0,
        )

    def insert(self, db: DB):
        """Inserts the record into the database.

        Args:
            db: The database object.
        """

        self.timestamp = int(datetime.datetime.now().timestamp())
        self.last_update = self.timestamp

        c = db.try_cursor()
        c.execute(
            f"INSERT INTO {DeviceRecord.table_name()} VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                self.device_id,
                self.sku,
                self.provisioning_state,
                self.timestamp,
                self.rma_unlock_token,
                self.dice_uds,
                self.cp_json,
                self.ft_json,
                self.last_update,
            ))
        db.commit()

    def update(self, db: DB):
        """Updates the record in the database.

        Args:
            db: The database object.
        """
        self.last_update = int(datetime.datetime.now().timestamp())

        c = db.try_cursor()
        keys = DeviceRecord.__annotations__.keys()
        update_params = [
            f"{field}=?" for field in keys if field != "device_id"
        ]
        update_vals = [
            getattr(self, field) for field in keys if field != "device_id"
        ]
        update_vals.append(self.device_id)
        c.execute(
            f"UPDATE {DeviceRecord.table_name()} SET {', '.join(update_params)} WHERE device_id=?",
            update_vals)
        db.commit()

    def upsert(self, db: DB):
        """Inserts or updates the record in the database.

        Args:
            db: The database object.
        """
        if DeviceRecord.query(db, self.device_id) is None:
            self.insert(db)
        else:
            self.update(db)
