# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Testpoint and Testplan classes for maintaining the testplan
"""

import re
import sys
from typing import Dict, List, Mapping, Optional, Set, TextIO, Union
from collections import defaultdict
from pathlib import Path

import hjson  # type: ignore
import mistletoe
from tabulate import tabulate

from JobTime import JobTime


class Result:
    '''The results for a single test'''

    def __init__(self,
                 name: str,
                 passing: int = 0,
                 total: int = 0,
                 job_runtime: Optional[JobTime] = None,
                 simulated_time: Optional[JobTime] = None):
        self.name = name
        self.passing = passing
        self.total = total
        self.job_runtime = job_runtime
        self.simulated_time = simulated_time
        self.mapped = False


class Element:
    """An element of the testplan.

    This is either a testpoint or a covergroup.
    """
    # Type of the testplan element. Must be set by the extended class.
    kind = "none"

    # Mandatory fields in a testplan element.
    fields = ["name", "desc"]

    def __init__(self, raw_dict: Mapping[str, object]) -> None:
        """Initialize the testplan element.

        raw_dict is the dictionary parsed from the HJSon file.
        """
        # 'tags' is an optional field in addition to the mandatory self.fields.
        self.tags = []  # type: List[str]

        # These fields will be overridden with items in raw_dict but setting
        # them here tells mypy about the types involved.
        self.name = ''
        self.desc = ''

        for field in self.fields:
            if field not in raw_dict:
                raise KeyError(f"Error: {self.kind} does not contain all of "
                               f"the required fields:\n{raw_dict}\nRequired:\n"
                               f"{self.fields}")

        # Set the k-v pairs in raw_dict as instance attributes.
        for k, v in raw_dict.items():
            setattr(self, k, v)

        # Verify things are in order.
        self._validate()

    def __str__(self) -> str:
        # Reindent the multiline desc with 4 spaces.
        desc = "\n".join(
            ["    " + line.lstrip() for line in self.desc.split("\n")])
        return (f"  {self.kind.capitalize()}: {self.name}\n"
                f"  Description:\n{desc}\n")

    def _validate(self) -> None:
        """Runs some basic consistency checks."""
        if not self.name:
            raise ValueError(f"Error: {self.kind.capitalize()} name cannot "
                             f"be empty:\n{self}")

        # "tags", if updated key must be list.
        if not isinstance(self.tags, list):
            raise ValueError(f"'tags' key in {self} is not a list.")

    def has_tags(self, tags: Set[str]) -> bool:
        """Checks if the provided tags match the tags originally set.

        tags is a list of tags that are we are filtering this testpoints with.
        Tags may be preceded with `-` to exclude the testpoints that contain
        that tag.

        Vacuously returns true if tags is an empty list.
        """
        if not tags:
            return True

        for tag in tags:
            if tag.startswith("-"):
                if tag[1:] in self.tags:
                    return False
            else:
                if tag not in self.tags:
                    return False

        return True


class Covergroup(Element):
    """A coverage model item.

    The list of covergroups defines the coverage model for the design. Each
    entry captures the name of the covergroup (suffixed with _cg) and a brief
    description describing what functionality is covered. It is recommended to
    include individual coverpoints and crosses in the description.
    """
    kind = "covergroup"

    def _validate(self) -> None:
        super()._validate()
        if not self.name.endswith("_cg"):
            raise ValueError(f"Error: Covergroup name {self.name} needs to "
                             "end with suffix \"_cg\".")


class Testpoint(Element):
    """An testcase entry in the testplan.

    A testpoint maps to a unique design feature that is planned to be verified.
    It captures following information:
    - name of the planned test
    - a brief description indicating intent, stimulus and checking procedure
    - the targeted stage
    - the list of actual developed tests that verify it
    """
    kind = "testpoint"
    fields = Element.fields + ["stage", "tests"]

    # Verification stages.
    stages = ("N.A.", "V1", "V2", "V2S", "V3")

    def __init__(self, raw_dict: Mapping[str, object]):
        # These will be overridden by the base class constructor (because their
        # names are in fields)
        self.stage = ""
        self.tests = []  # type: List[str]

        super().__init__(raw_dict)

        # List of Result objects indicating test results mapped to this
        # testpoint.
        self.test_results = []  # type: List[Result]

        # If tests key is set to ["N/A"], then don't map this testpoint to the
        # simulation results.
        self.not_mapped = False
        if self.tests == ["N/A"]:
            self.not_mapped = True

    def __str__(self) -> str:
        return super().__str__() + (f"  Stage: {self.stage}\n"
                                    f"  Tests: {self.tests}\n")

    def _validate(self) -> None:
        super()._validate()
        if self.stage not in Testpoint.stages:
            raise ValueError(f"Testpoint stage {self.stage} is "
                             f"invalid:\n{self}\nLegal values: "
                             f"Testpoint.stages")

        # "tests" key must be list.
        if not isinstance(self.tests, list):
            raise ValueError(f"'tests' key in {self} is not a list.")

    def do_substitutions(self, substitutions: Mapping[str, str]) -> None:
        '''Substitute {wildcards} in tests

        If tests have {wildcards}, they are substituted with the 'correct'
        values using the key=value pairs provided by the substitutions arg.
        Wildcards with no substitution arg are replaced by an empty string.

        substitutions is a dictionary of wildcard-replacement pairs.
        '''
        resolved_tests = []
        for test in self.tests:
            match = re.findall(r"{([A-Za-z0-9\_]+)}", test)
            if not match:
                resolved_tests.append(test)
                continue

            # 'match' is a list of wildcards used in the test. Get their
            # corresponding values.
            subst = {item: substitutions.get(item, "") for item in match}

            resolved = [test]
            for item, value in subst.items():
                values = value if isinstance(value, list) else [value]
                resolved = [
                    t.replace(f"{{{item}}}", v) for t in resolved
                    for v in values
                ]
            resolved_tests.extend(resolved)

        self.tests = resolved_tests

    def map_test_results(self, test_results: List[Result]) -> None:
        """Map test results to tests against this testpoint.

        Given a list of test results find the ones that match the tests listed
        in this testpoint and buiild a structure. If no match is found, or if
        self.tests is an empty list, indicate 0/1 passing so that it is
        factored into the final total.
        """
        # If no written tests were indicated for this testpoint, then reuse
        # the testpoint name to count towards "not run".
        if not self.tests:
            self.test_results = [Result(name=self.name)]
            return

        # Skip if this testpoint is not meant to be mapped to the simulation
        # results.
        if self.not_mapped:
            return

        for tr in test_results:
            assert isinstance(tr, Result)
            if tr.name in self.tests:
                tr.mapped = True
                self.test_results.append(tr)

        # Did we map all tests in this testpoint? If we are mapping the full
        # testplan, then count the ones not found as "not run", i.e. 0 / 0.
        tests_mapped = [tr.name for tr in self.test_results]
        for test in self.tests:
            if test not in tests_mapped:
                self.test_results.append(Result(name=test))


class Testplan:
    """The full testplan

    The list of Testpoints and Covergroups make up the testplan.
    """

    rsvd_keywords = ["import_testplans", "testpoints", "covergroups"]
    element_cls = {'testpoint': Testpoint, 'covergroup': Covergroup}

    @staticmethod
    def _parse_hjson(filename: Path) -> Dict[str, object]:
        """Parses an input file with HJson and returns a dict."""
        try:
            return hjson.load(open(filename, 'r'))  # type: ignore
        except IOError as e:
            print(f"IO Error when opening file {filename}\n{e}")
        except hjson.scanner.HjsonDecodeError as e:
            print(f"Error: Unable to decode HJSON with file {filename}:\n{e}")
        sys.exit(1)

    @staticmethod
    def _create_testplan_elements(kind: str,
                                  raw_dicts_list: List[Mapping[str, object]],
                                  tags: Set[str]) -> List[Element]:
        """Creates testplan elements from the list of raw dicts.

        kind is either 'testpoint' or 'covergroup'.
        raw_dicts_list is a list of dictionaries extracted from the HJson file.
        """
        items = []
        item_names = set()
        for dict_entry in raw_dicts_list:
            try:
                item = Testplan.element_cls[kind](dict_entry)
            except KeyError as e:
                print(f"Error: {kind} arg is invalid.\n{e}")
                sys.exit(1)
            except ValueError as e:
                print(f"{kind}\n{dict_entry}\n{e}")
                sys.exit(1)

            if item.name in item_names:
                print(f"Error: Duplicate {kind} item found with name: "
                      f"{item.name}")
                sys.exit(1)

            # Filter out the item by tags if provided.
            if item.has_tags(tags):
                items.append(item)
                item_names.add(item.name)
        return items

    @staticmethod
    def _get_percentage(value: int, total: int) -> str:
        """Returns a string representing percentage upto 2 decimal places."""
        if total == 0:
            return "-- %"
        perc = value / total * 100 * 1.0
        return "{0:.2f} %".format(round(perc, 2))

    @staticmethod
    def get_dv_style_css() -> str:
        """Returns text with HTML CSS style for a table."""
        return ("<style>\n"
                "table.dv {\n"
                "    border: 1px solid black;\n"
                "    border-collapse: collapse;\n"
                "    width: 100%;\n"
                "    text-align: left;\n"
                "    vertical-align: middle;\n"
                "    display: table;\n"
                "    font-size: smaller;\n"
                "}\n"
                "table.dv th, td {\n"
                "    border: 1px solid black;\n"
                "}\n"
                "</style>\n")

    def __str__(self) -> str:
        lines = [f"Name: {self.name}\n"]
        lines += ["Testpoints:"]
        lines += [f"{t}" for t in self.testpoints]
        lines += ["Covergroups:"]
        lines += [f"{c}" for c in self.covergroups]
        return "\n".join(lines)

    def __init__(self,
                 filename: Union[str, Path],
                 repo_top: Optional[Path] = None,
                 name: Optional[str] = None):
        """Initialize the testplan.

        filename is the HJson file that captures the testplan. It may be
        suffixed with tags separated with a colon delimiter to filter the
        testpoints. For example: path/too/foo_testplan.hjson:bar:baz
        repo_top is an optional argument indicating the path to top level repo
        / project directory. It is used with filename arg.
        name is an optional argument indicating the name of the testplan / DUT.
        It overrides the name set in the testplan HJson.
        """
        self.name = ''
        self.testpoints = []  # type: List[Testpoint]
        self.covergroups = []  # type: List[Element]
        self.test_results_mapped = False

        # Split the filename into filename and tags, if provided.
        split = str(filename).split(":")
        filename = Path(split[0])
        tags = set(split[1:])

        if filename.exists():
            self._parse_testplan(filename, tags, repo_top)

        if name is not None:
            self.name = name

        if not self.name:
            print("Error: the testplan 'name' is not set!")
            sys.exit(1)

        # Represents current progress towards each stage. Stage = N.A.
        # is used to indicate the unmapped tests.
        #
        # Note: This really needs to be turned into something a little more
        # heterogeneous than a nested dict. At the moment, each progress[stage]
        # is a dictionary with four string fields (total, written, passing,
        # progress). The associated values have types int, int, int, float,
        # except that the last field gets turned into a str in map_test_results
        # and map_covergroups. To silence errors from mypy, we have to use type
        # ignore in several places when interacting with this rather-ill-typed
        # dictionary.
        self.progress = {}
        for key in Testpoint.stages:
            self.progress[key] = {
                "total": 0,
                "written": 0,
                "passing": 0,
                "progress": 0.0,
            }

    @staticmethod
    def _get_imported_testplan_paths(parent_testplan: Path,
                                     imported_testplans: List[Path],
                                     repo_top: Path) -> List[Path]:
        '''Parse imported testplans with correctly set paths.

        Paths of the imported testplans can be set relative to repo_top
        or relative to the parent testplan importing it. Path anchored to
        the repo_top has higher precedence. If the path is not relative to
        either, we check if the path is absolute (which must be avoided!),
        else we raise an exception.

        parent_testplan is the testplan currently being processed which
        importing the sub-testplans.
        imported_testplans is the list of testplans it imports - retrieved
        directly from its Hjson file.
        repo_top is the path to the repository's root directory.

        Returns a list of imported testplans with correctly set paths.
        Raises FileNotFoundError if the relative path to the testplan is
        not anchored to repo_top or the parent testplan.
        '''
        result = []
        for testplan in imported_testplans:
            path = repo_top / testplan
            if path.exists():
                result.append(path)
                continue

            path = parent_testplan.parent / testplan
            if path.exists():
                result.append(path)
                continue

            # In version-controlled codebases, references to absolute paths
            # must not exist. This usecase is supported anyway.
            path = Path(testplan)
            if path.exists():
                result.append(path)
                continue

            raise FileNotFoundError(f"Testplan {testplan} imported by "
                                    f"{parent_testplan} does not exist.")

        return result

    @staticmethod
    def as_string(raw: object, what: str) -> str:
        '''Return raw, cast to a string'''
        if not isinstance(raw, str):
            raise TypeError(f'{what} was {raw!r}, not a string.')
        return raw

    @staticmethod
    def as_int(raw: object, what: str) -> int:
        '''Return raw, cast to an int'''
        if isinstance(raw, int):
            return raw
        elif isinstance(raw, str):
            try:
                return int(raw)
            except ValueError:
                raise TypeError(f'{what} was {raw!r}, not denoting an integer')
        else:
            raise TypeError(f'{what} was {raw!r}, not an integer.')

    @staticmethod
    def as_string_map(raw: object, what: str) -> Mapping[str, object]:
        '''Return raw, cast into a dict from strings'''
        if not isinstance(raw, dict):
            raise TypeError(f'{what} was {raw!r}, not a dict.')
        cast = {}  # type: Dict[str, str]
        for k, v in raw.items():
            if not isinstance(k, str):
                raise TypeError(f'One key of {what} was {k!r}, not a str.')
            cast[k] = v
        return cast

    @staticmethod
    def as_list(raw: object, what: str) -> List[object]:
        '''Return raw, cast into a list'''
        if not isinstance(raw, list):
            raise TypeError(f'{what} was {raw!r}, not a list.')
        return raw

    @staticmethod
    def as_path_list(raw: object, what: str) -> List[Path]:
        '''Return raw, cast to a list of Path objects'''
        if not isinstance(raw, list):
            raise TypeError(f'{what} was {raw!r}, not a list.')
        paths = []  # type: List[Path]
        for idx, elt in enumerate(raw):
            try:
                paths.append(Path(elt))
            except TypeError:
                raise TypeError(f'Element {idx} of {what} was {elt!r}, '
                                'which cannot be read as a Path.') from None
        return paths

    @staticmethod
    def as_string_list(raw: object, what: str) -> List[str]:
        '''Return raw cast into a list of strings'''
        return [Testplan.as_string(elt, f'Item with index {idx} of {what}')
                for idx, elt in enumerate(Testplan.as_list(raw, what))]

    @staticmethod
    def as_string_map_list(raw: object, what: str) -> List[Mapping[str, object]]:
        '''Return raw cast into a list dicts keyed by strings.'''
        return [Testplan.as_string_map(elt, f'Item with index {idx} of {what}')
                for idx, elt in enumerate(Testplan.as_list(raw, what))]

    def _parse_testplan(self,
                        filename: Path,
                        tags: Set[str],
                        repo_top: Optional[Path] = None) -> None:
        '''Parse testplan Hjson file and create the testplan elements.

        It creates the list of testpoints and covergroups extracted from the
        file.

        filename is the path to the testplan file written in HJson format.
        repo_top is an optional argument indicating the path to repo top.
        '''
        if repo_top is None:
            # Assume dvsim's original location: $REPO_TOP/util/dvsim.
            repo_top = Path(__file__).parent.parent.parent.resolve()

        obj = Testplan._parse_hjson(filename)

        parsed = set()
        parent_testplan = Path(filename)

        imported_paths = \
            Testplan.as_path_list(obj.get("import_testplans", []),
                                  f'import_testplans field at {filename}')
        imported_testplans = self._get_imported_testplan_paths(parent_testplan,
                                                               imported_paths,
                                                               repo_top)

        while imported_testplans:
            testplan = repo_top / imported_testplans.pop(0)
            if testplan in parsed:
                print(f"Error: encountered the testplan {testplan} again, "
                      "which was already parsed. Please check for circular "
                      "dependencies.")
                sys.exit(1)
            parsed.add(testplan)
            data = self._parse_hjson(testplan)
            further_imports = \
                Testplan.as_path_list(data.get("import_testplans", []),
                                      f'import_testplans field at {testplan}')

            imported_testplans.extend(
                self._get_imported_testplan_paths(testplan,
                                                  further_imports, repo_top))
            obj = _merge_dicts(obj, data)

        self.name = Testplan.as_string(obj.get("name"),
                                       f'name field at {testplan}')

        testpoints = \
            Testplan.as_string_map_list(obj.get("testpoints", []),
                                        f'testpoints field at {testplan}')
        self.testpoints = self._create_testplan_elements(
            'testpoint', testpoints, tags)  # type: ignore

        covergroups = \
            Testplan.as_string_map_list(obj.get("covergroups", []),
                                        f'covergroups field at {testplan}')
        self.covergroups = self._create_testplan_elements(
            'covergroup', covergroups, set())

        if not testpoints and not covergroups:
            print(f"Error: No testpoints or covergroups found in {filename}")
            sys.exit(1)

        # Any variable in the testplan that is not a recognized HJson field can
        # be used as a substitution variable.
        substitutions = {
            k: v
            for k, v in obj.items()
            if k not in self.rsvd_keywords and isinstance(v, str)
        }
        for tp in self.testpoints:
            tp.do_substitutions(substitutions)

        self._sort()

    def _sort(self) -> None:
        """Sort testpoints by stage and covergroups by name."""
        self.testpoints.sort(key=lambda x: x.stage)
        self.covergroups.sort(key=lambda x: x.name)

    def get_stage_regressions(self) -> List[Dict[str, object]]:
        regressions = defaultdict(set)
        for tp in self.testpoints:
            if tp.not_mapped:
                continue
            if tp.stage in tp.stages[1:]:
                regressions[tp.stage].update({t for t in tp.tests if t})

        # Build regressions dict into a hjson like data structure
        return [{
            "name": ms,
            "tests": list(regressions[ms])
        } for ms in regressions]

    def write_testplan_doc(self, output: TextIO) -> None:
        """Write testplan documentation in markdown from the hjson testplan."""

        stages = {}  # type: Dict[str, List[Testpoint]]
        for tp in self.testpoints:
            stages.setdefault(tp.stage, list()).append(tp)

        output.write("# Testplan\n\n## Testpoints\n\n")
        for (stage, testpoints) in stages.items():
            output.write(f"### Stage {stage} Testpoints\n\n")
            for tp in testpoints:
                output.write(f"#### `{tp.name}`\n\n")
                if len(tp.tests) == 0:
                    output.write("No Tests Implemented")
                elif len(tp.tests) == 1:
                    output.write(f"Test: `{tp.tests[0]}`")
                else:
                    output.write("Tests:\n")
                    output.writelines([f"- `{test}`\n" for test in tp.tests])

                output.write("\n\n" + tp.desc.strip() + "\n\n")

        if self.covergroups:
            output.write("## Covergroups\n\n")
            for covergroup in self.covergroups:
                output.write(f"### {covergroup.name}\n\n{covergroup.desc.strip()}\n\n")

    def map_test_results(self, test_results: List[Result]) -> None:
        """Map test results to testpoints."""
        # Maintain a list of tests we already counted.
        tests_seen = set()
        totals = {}  # type: Dict[str, Testpoint]

        def _process_testpoint(testpoint: Testpoint) -> None:
            """Computes the testplan progress and the sim footprint.

            totals is a list of Testpoint items that represent the total number
            of tests passing for each stage. The sim footprint is simply
            the sum total of all tests run in the simulation, counted for each
            stage and also the grand total.
            """
            ms = testpoint.stage
            for tr in testpoint.test_results:
                if not tr:
                    continue

                if tr.name in tests_seen:
                    continue

                tests_seen.add(tr.name)
                # Compute the testplan progress.
                self.progress[ms]["total"] += 1
                if tr.total != 0:
                    if tr.passing == tr.total:
                        self.progress[ms]["passing"] += 1
                    self.progress[ms]["written"] += 1

                # Compute the stage total & the grand total.
                totals[ms].test_results[0].passing += tr.passing
                totals[ms].test_results[0].total += tr.total
                if ms != "N.A.":
                    totals["N.A."].test_results[0].passing += tr.passing
                    totals["N.A."].test_results[0].total += tr.total

        # Create testpoints to represent the total for each stage & the
        # grand total.
        for ms in Testpoint.stages:
            arg = {
                "name": "N.A.",
                "desc": f"Total {ms} tests",
                "stage": ms,
                "tests": [],
            }
            totals[ms] = Testpoint(arg)
            totals[ms].test_results = [Result("**TOTAL**")]

        # Create unmapped as a testpoint to represent tests from the simulation
        # results that could not be mapped to the testpoints.
        arg = {
            "name": "Unmapped tests",
            "desc": "Unmapped tests",
            "stage": "N.A.",
            "tests": [],
        }
        unmapped = Testpoint(arg)

        # Now, map the simulation results to each testpoint.
        for tp in self.testpoints:
            tp.map_test_results(test_results)
            _process_testpoint(tp)

        # If we do have unmapped tests, then count that too.
        unmapped.test_results = [tr for tr in test_results if not tr.mapped]
        _process_testpoint(unmapped)

        # Add stage totals back into 'testpoints' and sort.
        for ms in Testpoint.stages[1:]:
            self.testpoints.append(totals[ms])
        self._sort()

        # Append unmapped and the grand total at the end.
        if unmapped.test_results:
            self.testpoints.append(unmapped)
        self.testpoints.append(totals["N.A."])

        # Compute the progress rate for each stage.
        for ms in Testpoint.stages:
            stat = self.progress[ms]

            # Remove stages that are not targeted.
            if stat["total"] == 0:
                self.progress.pop(ms)
                continue

            stat["progress"] = self._get_percentage(stat["passing"],  # type: ignore
                                                    stat["total"])  # type: ignore

        self.test_results_mapped = True

    def map_covergroups(self, cgs_found: List[str]) -> None:
        """Map the covergroups found from simulation to the testplan.

        For now, this does nothing more than 'check off' the covergroup
        found from the simulation results with the coverage model in the
        testplan by updating the progress dict.

        cgs_found is a list of covergroup names extracted from the coverage
        database after the simulation is run with coverage enabled.
        """

        if not self.covergroups:
            return

        written = 0
        total = 0
        for cg in self.covergroups:
            total += 1
            if cg.name in cgs_found:
                written += 1

        self.progress["Covergroups"] = {
            "total": total,
            "written": written,
            "passing": written,
            "progress": self._get_percentage(written, total)  # type: ignore
        }

    def get_test_results_table(self, map_full_testplan: bool = True) -> str:
        """Return the mapped test results into a markdown table."""

        assert self.test_results_mapped, "Have you invoked map_test_results()?"
        header = [
            "Stage", "Name", "Tests", "Max Job Runtime", "Simulated Time",
            "Passing", "Total", "Pass Rate"
        ]
        colalign = ('center', ) * 2 + ('left', ) + ('center', ) * 5
        table = []
        for tp in self.testpoints:
            stage = "" if tp.stage == "N.A." else tp.stage
            tp_name = "" if tp.name == "N.A." else tp.name
            for tr in tp.test_results:
                if tr.total == 0 and not map_full_testplan:
                    continue
                pass_rate = self._get_percentage(tr.passing, tr.total)

                job_runtime = "" if tr.job_runtime is None else str(
                    tr.job_runtime)
                simulated_time = "" if tr.simulated_time is None else str(
                    tr.simulated_time)

                table.append([
                    stage, tp_name, tr.name, job_runtime, simulated_time,
                    tr.passing, tr.total, pass_rate
                ])
                stage = ""
                tp_name = ""

        text = "\n### Test Results\n"
        text += tabulate(table,
                         headers=header,
                         tablefmt="pipe",
                         colalign=colalign)
        text += "\n"
        return text

    def get_progress_table(self) -> str:
        """Returns the current progress of the effort towards the testplan."""

        assert self.test_results_mapped, "Have you invoked map_test_results()?"
        header = []  # type: List[str]
        table = []
        for key in self.progress:
            stat = self.progress[key]
            values = [v for v in stat.values()]  # type: List[object]
            if not header:
                header = ["Items"] + [k.capitalize() for k in stat]
            col1 = [key]  # type: List[object]
            table.append(col1 + values)

        text = "\n### Testplan Progress\n"
        colalign = (("center", ) * len(header))
        text += tabulate(table,
                         headers=header,
                         tablefmt="pipe",
                         colalign=colalign)
        text += "\n"
        return text

    def get_cov_results_table(self,
                              cov_results: List[Mapping[str, object]]) -> str:
        """Returns the coverage in a table format.

        cov_results is a list of dicts with name and result keys, representing
        the name of the coverage metric and the result in decimal / fp value.
        """

        if not cov_results:
            return ""

        cov_header: List[str] = []
        cov_values: List[object] = []

        for c in cov_results:
            if 'name' not in c:
                print(f"Item of coverage results with no name: {c}",
                      file=sys.stderr)
                sys.exit(1)
            if 'result' not in c:
                print(f"Item of coverage results with no result: {c}",
                      file=sys.stderr)
                sys.exit(1)

            name = c['name']
            result = c['result']

            if not isinstance(name, str):
                print(f"Item of coverage results with non-string name: {name}",
                      file=sys.stderr)
                sys.exit(1)

            cov_header.append(name.capitalize())
            cov_values.append(result)

        colalign = (("center", ) * len(cov_header))
        text = "\n### Coverage Results\n"
        text += tabulate([cov_values],
                         headers=cov_header,
                         tablefmt="pipe",
                         colalign=colalign)
        text += "\n"
        return text

    def get_test_results_summary(self) -> Dict[str, object]:
        """Returns the final total as a summary."""
        assert self.test_results_mapped, "Have you invoked map_test_results()?"

        # The last item in tespoints is the final sum total. We use that to
        # return the results summary as a dict.
        total = self.testpoints[-1]
        assert total.name == "N.A."
        assert total.stage == "N.A."

        tr = total.test_results[0]

        result = {}  # type: Dict[str, object]
        result["Name"] = self.name.upper()
        result["Passing"] = tr.passing
        result["Total"] = tr.total
        result["Pass Rate"] = self._get_percentage(tr.passing, tr.total)
        return result

    def get_sim_results(self, sim_results_file: Path, fmt: str = "md") -> str:
        """Returns the mapped sim result tables in HTML formatted text.

        The data extracted from the sim_results table HJson file is mapped into
        a test results, test progress, covergroup progress and coverage tables.

        fmt is either 'md' (markdown) or 'html'.
        """
        assert fmt in ["md", "html"]
        sim_results = Testplan._parse_hjson(sim_results_file)

        test_results = []

        test_results_what = f'test_results in {sim_results_file}'
        raw_test_results = \
            Testplan.as_list(sim_results.get("test_results", []),
                             test_results_what)
        for idx, item in enumerate(raw_test_results):
            item_what = f'Item {idx} of {test_results_what}'
            if not isinstance(item, dict):
                raise TypeError(f'{item_what} is {item!r}, not a dict')
            name = Testplan.as_string(item.get('name'), f'name of {item_what}')
            passing = Testplan.as_int(item.get('passing', 0),
                                      f'passing of {item_what}')

            try:
                tr = Result(name, passing, item["total"])
                test_results.append(tr)
            except KeyError as e:
                print(f"Error: data in {sim_results_file} is malformed!\n{e}")
                sys.exit(1)

        self.map_test_results(test_results)
        covergroups = \
            Testplan.as_string_list(sim_results.get("covergroups", []),
                                    f'covergroups in {sim_results_file}')
        self.map_covergroups(covergroups)

        text = "# Simulation Results\n"
        text += "## Run on {}\n".format(sim_results["timestamp"])
        text += self.get_test_results_table()
        text += self.get_progress_table()

        cov_results = \
            Testplan.as_string_map_list(sim_results.get("cov_results", []),
                                        f'cov_results in {sim_results_file}')
        text += self.get_cov_results_table(cov_results)

        if fmt == "html":
            text = self.get_dv_style_css() + mistletoe.markdown(text)
            text = text.replace("<table>", "<table class=\"dv\">")
        return text


def _merge_dicts(list1: Dict[str, object],
                 list2: Dict[str, object],
                 use_list1_for_defaults: bool = True) -> Dict[str, object]:
    '''Merge 2 dicts into one

    This function takes 2 dicts as args list1 and list2. It recursively merges
    list2 into list1 and returns list1. The recursion happens when the
    value of a key in both lists is a dict. If the values of the same key in
    both lists (at the same tree level) are of dissimilar type, then there is a
    conflict and an error is thrown. If they are of the same scalar type, then
    the third arg "use_list1_for_defaults" is used to pick the final one.
    '''
    for key, item2 in list2.items():
        item1 = list1.get(key)
        if item1 is None:
            list1[key] = item2
            continue

        # Both dictionaries have an entry for this key. Are they both lists? If
        # so, append.
        if isinstance(item1, list) and isinstance(item2, list):
            list1[key] = item1 + item2
            continue

        # Are they both dictionaries? If so, recurse.
        if isinstance(item1, dict) and isinstance(item2, dict):
            _merge_dicts(item1, item2)
            continue

        # We treat other types as atoms. If the types of the two items are
        # equal pick one or the other (based on use_list1_for_defaults).
        if isinstance(item1, type(item2)) and isinstance(item2, type(item1)):
            list1[key] = item1 if use_list1_for_defaults else item2
            continue

        # Oh no! We can't merge this.
        print("ERROR: Cannot merge dictionaries at key {!r} because items "
              "have conflicting types ({} in 1st; {} in 2nd).".format(
                  key, type(item1), type(item2)))
        sys.exit(1)

    return list1
