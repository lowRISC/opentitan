# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Unittests for db.py module."""

import random
import string
import unittest

import db


def random_string_build(length=1000) -> str:
    """Returns a random string of the given length.

    Args:
        length: The length of the random string.
    Returns:
        A random string of the given length.
    """
    characters = string.ascii_letters + string.digits + string.punctuation
    return ''.join(random.choice(characters) for _ in range(length))


class TestDeviceRecord(unittest.TestCase):

    def setUp(self):
        self.db_config = db.DBConfig(db_path=':memory:')
        self.db = db.DB(self.db_config)
        db.DeviceRecord.create_table(self.db)

    def _random_device_record(self) -> db.DeviceRecord:
        return db.DeviceRecord(device_id=random_string_build(),
                               sku=random_string_build(),
                               provisioning_state=random_string_build(),
                               timestamp=-1,
                               rma_unlock_token=random_string_build(),
                               dice_uds=random_string_build(),
                               cp_json=random_string_build(),
                               ft_json=random_string_build(),
                               last_update=-1)

    def test_insert_and_query(self):
        device_record = self._random_device_record()
        device_record.insert(self.db)
        got_device_record = db.DeviceRecord.query(self.db,
                                                  device_record.device_id)
        self.assertEqual(device_record, got_device_record)

    def test_update(self):
        device_record = self._random_device_record()
        device_record.insert(self.db)
        device_record.provisioning_state = 'UNLOCKED'
        device_record.update(self.db)
        got_device_record = db.DeviceRecord.query(self.db,
                                                  device_record.device_id)
        device_record.last_update = got_device_record.last_update
        self.assertEqual(device_record, got_device_record)

    def test_upsert(self):
        device_record = self._random_device_record()
        device_record.upsert(self.db)
        got_device_record = db.DeviceRecord.query(self.db,
                                                  device_record.device_id)
        self.assertEqual(device_record, got_device_record)

        device_record.provisioning_state = 'UNLOCKED'
        device_record.upsert(self.db)
        got_device_record = db.DeviceRecord.query(self.db,
                                                  device_record.device_id)

        device_record.last_update = got_device_record.last_update
        self.assertEqual(device_record, got_device_record)

    def test_query_all(self):
        device_records = [self._random_device_record() for _ in range(10)]
        for device_record in device_records:
            device_record.insert(self.db)
        got_device_records = db.DeviceRecord.query_all(self.db)
        self.assertEqual(device_records, got_device_records)


if __name__ == '__main__':
    unittest.main()
