# Silicon nightly runner

## Summary
This a tool that pull the latest changes in the `Eargrey_es_sival` branch, runs the Sival test suite and upload the results to a google sheets.

## Requirements
You need to get a google OAuth token as described [here](https://docs.gspread.org/en/v6.0.0/oauth2.html#for-end-users-using-oauth-client-id).
Once you have the user account token in a json file, choose a folder to store it. The folder `$(HOME)/.config/silicon-nightly-runner/` is recommended.

You also need to create a config file in `$(HOME)/.config/silicon-nightly-runner/config.json` with the following format:
```json
{
    "ot_home" : "path/to/opentitan/repo",
    "google_oauth_file": "path/to/token/user-account.json",
    "google_service_file": "path/to/token/of/service/account",
    "sheet_id": "spreadsheet-id",
    "sheet_tab": "tab-name",
    "sheet_row_offset": 2,
    "sheet_column_offset": 4,
    "sheet_testname_column_offset": 3
}
```

Where:

 1. **ot_home** : Is the path to a clone of Opentitan repository.
 1. **google_oauth_file**: Is the path to the google OAuth token in case of user ID will be used.
 1. **google_service_file**: Is the path to the service account token in case of service account.
 1. **sheet_id**: Is the id of the spread sheet, which is part of the sheet url, i.e. `https://docs.google.com/spreadsheets/d/<id>`
 1. **sheet_tab**: The tab name in the sheet, it will be created if doesn't exist.
 1. **sheet_row_offset**: Is the offset row where the results should start to be populated. Normally the first row is reserved for the header.
 1. **sheet_column_offset**: Is the offset column where the results should start to be populated.
 1. **sheet_testname_column_offset**: Is the offset of the column where the tests names should be.

## Installing a nightly job
Create a cronjob using the command:
 ```sh
 crontab -e
 ```
The cronjob configuration file should look like:

 ```console
$crontab -l

SHELL=/bin/bash

# 7:00am each day
00 7 * * * cd <path/to/opentitan/home>/utils/silicon-nightly-runner && mkdir -p ./logs && ./run_tests.sh 2>&1 | tee "./logs/$(date +\%Y-\%m-\%d)-run-tests.log" && ./parse_test_results.sh 2>&1 | tee "./logs/$(date +\%Y-\%m-\%d)-parse-results.log"
 ```

 ## Uploading results
 In case the upload part fails for some reason, they can be uploaded later, as the results are stored in the folder `archive`.
 The script `upload_results.sh` can upload all the results in `archive` or the results for only one day.

 To upload all the results in `archive`:
 ```sh
 ./upload_results.sh
 ```

To upload a specific day:
 ```sh
 ./upload_results.sh ./archive/<yyyy-mm-dd>/test.xml
 ```
