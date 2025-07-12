./ci/scripts/python-lint.sh master
./ci/scripts/mypy.sh 
./ci/scripts/check-licence-headers.sh master
ruff check
