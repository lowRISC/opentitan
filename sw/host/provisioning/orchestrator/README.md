# Provisioning Orchestrator

## Connecting to remote database

The provisioning orchestrator supports storing device records in a Firestore database on Google Cloud.
The following steps are required to use this functionality.

First, install the script's additional dependencies, preferably in a virtual environment:

```console
python3 -m venv orchestrator_env
source orchestrator_env/bin/activate
pip install -r requirements.txt
```

Next, authenticate with Google Cloud using the `gcloud` CLI utility:

```console
gcloud auth application-default login
```

When you run `orchestrator.py`, supply an additional argument `--cloud_project` which provides the name of a Google Cloud project with a Firestore database named `(default)`.

```console
python3 orchestrator.py --db_file local.db --cloud_project my-project ...
```

Records that fail to upload for any reason will be preserved in a local SQLite database.
The `update_remote_db.py` script can be used to sync those to the Firestore database at a later time.

```console
python3 update_remote_db.py local.db --project my-project
```
