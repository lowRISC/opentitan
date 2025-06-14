#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script uses the GraphQL GitHub API to compute committer statistics for
# the OpenTitan project.
#
# Usage:
#  - Set the following environment variables:
#    - "GH_GRAPHQL_API_PAT": this is a personal access token generate for your
#       GitHub account that will enable this script to use the GitHub GraphQL
#       API. Follow the instructions here on how to create one:
#       https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens
# - Run this script with no parameters. Optionally use `--log-progress` to
#   output query progress, as the paginated queries can take some time to run.
#   You can use `--filter` to filter existing and historical committers, to
#   assist in finding potential candidates for future committers.

import git
import json
import os
import sys
import requests
import time
import webbrowser
from collections import Counter
from enum import Enum
from pathlib import Path
from tabulate import tabulate
from typing import Optional, Dict, Tuple, Iterable, Any


# OpenTitan main repo URL
OT_REPO_URL = "https://github.com/lowRISC/opentitan"

# GraphQL endpoint / query for commits, PRs, and reviews
GH_GRAPHQL_API_ENDPOINT = "https://api.github.com/graphql"

# The location of the top of the repository from this file
REPO_TOP = Path(__file__).parents[3]

# The location of the COMMITTERS file within the repo
COMMITTERS_FILE = "COMMITTERS"
COMMITTERS_PATH = REPO_TOP / COMMITTERS_FILE

# The location of the output HTML file to generate if using HtmlDisplay output
HTML_OUTPUT_FILE = "committer_stats.html"
HTML_OUTPUT_PATH = REPO_TOP / HTML_OUTPUT_FILE


class CommitterStatsReporter:

    # Different formats the report can be output in
    class OutputFormat(Enum):
        Table = "table"
        Json = "json"
        HtmlOutput = "html_output"
        HtmlDisplay = "html_display"

        def __str__(self):
            return self.value

    # A list of users to ignore from calculated statistics.
    IgnoredUsers = [
        "github-actions",  # Automated CI
    ]

    def __init__(
        self,
        owner: str,
        repo: str,
        github_token: Optional[str] = None,
        log_progress: bool = False,
    ):
        """Constructor for the CommitterStatsReporter.

        Args:
            owner (str): The owner of the repository to get stats for.
            repo (str): The repository to retrieve stats for.
            github_token (Optional[str], optional): The Github Personal Access Token
            (PAT) to use for authorization. Defaults to None.
            log_progress (bool, optional): Whether to log progress messages
            whilst querying the GraphQL API. Defaults to False.
        """
        self.owner = owner
        self.repo = repo
        self.__github_token = github_token
        self.log_progress = log_progress
        self.commit_data = None
        self.pr_data = None
        self.review_data = None

    def _run_github_graphql_query(
        self, query: str, variables: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """Run a query on the Github GraphQL API.

        Args:
            query (str): The GraphQL query to post.
            variables (Optional[Dict[str, Any]], optional): The variables to insert
            into the query. Defaults to None.
        Returns:
            Dict[str, Any]: The JSON response from the Github API.
        """
        headers = {"Content-Type": "application/json"}
        if self.__github_token is not None:
            # Note that we use the 'bearer' scheme
            headers["Authorization"] = f"Bearer {self.__github_token}"

        payload = {"query": query}
        if variables is not None:
            payload["variables"] = variables

        # Repeatedly try to request the data from the Github GraphQL API,
        # respecting rate limit requests and using an exponential timeout
        # scheme to handle connection issues.
        response_wait_time = None
        while True:
            try:
                response = requests.post(
                    GH_GRAPHQL_API_ENDPOINT, json=payload, headers=headers
                )
                if response_wait_time is not None:
                    time.sleep(response_wait_time)
                response.raise_for_status()
            except requests.exceptions.HTTPError as e:
                print(f"HTTP Error: {e}\nWaiting 5 seconds and retrying...")
                time.sleep(5)
                continue
            except requests.exceptions.ConnectTimeout:
                if response_wait_time is None:
                    response_wait_time = 1
                else:
                    response_wait_time *= 2
                    print(
                        "Unable to connect to Github API. Retrying with a",
                        f"wait of {response_wait_time} seconds...",
                    )
                continue

            # Check response status code
            if (
                response.status_code == 403
                and "X-RateLimit-Remaining" in response.headers
            ):
                # If we hit a rate limit, sleep for the suggested time.
                remaining_reqs = int(response.headers["X-RateLimit-Remaining"])
                reset = int(response.headers.get("X-RateLimit-Reset", 0))
                if remaining_reqs == 0:
                    wait_time = max(reset - time.time(), 5)
                    if self.log_progress:
                        print(
                            f"Rate limit exceeded - sleeping for {int(wait_time)}",
                            "seconds before retrying...",
                        )
                    time.sleep(wait_time)
                    continue
            elif response.status_code != 200:  # response =/= HTTP OK
                print(f"Query failed with code {response.status_code}: {response.text}")
                sys.exit(-1)

            # Also handle GraphQL errors from bad queries / API changes
            data = response.json()
            if "errors" in data:
                print(f"GraphQL error: {data['errors']}")

            return data

    def get_commit_authors(
        self,
        page_limit: Optional[int] = None,
    ) -> Counter[str]:
        """Get information about the authors of commits in a Github repository.

        Args:
            page_limit (Optional[int], optional): A limit for the number of (100-item)
            pages to query. Will then return the first N pages, which is useful for
            testing. Defaults to None, meaning all commits are searched.

        Returns:
            Counter[str]: The count of commits per committer.
        """
        if self.log_progress:
            print("Retrieving commit information...")
        authors = Counter()
        cursor = None

        query = """
        query getRepoData($owner: String!, $repo: String!, $cursor: String) {
          repository(owner: $owner, name: $repo) {
            defaultBranchRef {
              target {
                ... on Commit {
                  history(first: 100, after: $cursor) {
                    nodes {
                      author {
                        user {
                          login
                        }
                      }
                    }
                    pageInfo {
                      hasNextPage
                      endCursor
                    }
                  }
                }
              }
            }
          }
        }
        """

        pages_traversed = 0
        while True:
            variables = {"owner": self.owner, "repo": self.repo, "cursor": cursor}
            data = self._run_github_graphql_query(query, variables=variables)
            pages_traversed += 1

            try:
                history = data["data"]["repository"]["defaultBranchRef"]["target"][
                    "history"
                ]
                for node in history["nodes"]:
                    author_user = node["author"]["user"]
                    author = author_user["login"] if author_user else "Unknown Author"
                    if author:
                        authors[author] += 1

                if self.log_progress:
                    print(
                        f"Searched {sum(authors.values())} commits for author information..."
                    )

                if not history["pageInfo"]["hasNextPage"] or (
                    page_limit and pages_traversed >= page_limit
                ):
                    break
                cursor = history["pageInfo"]["endCursor"]
            except KeyError as e:
                print(
                    f"Error accessing data: {e}. Check the structure of the GraphQL response."
                )
                # Print the full response for debugging
                print(json.dumps(data, indent=2))
                return Counter()
            except TypeError as e:
                print(f"Error processing data: {e}. Possibly no commits/PRs/reviews.")
                print(json.dumps(data, indent=2))
                return Counter()

        # Remove ignored users (e.g. automated CI)
        for user in self.IgnoredUsers:
            if user in authors:
                del authors[user]

        return authors

    def get_pr_and_review_authors(
        self,
        page_limit: Optional[int] = None,
    ) -> Tuple[Counter[str], Counter[str]]:
        """Get information about the authors of PRs and reviews on those PRs in a
        Github repository.

        Args:
            page_limit (Optional[int], optional): A limit for the number of (100-item)
            pages to query. Will then return the first N pages, which is useful for
            testing. Defaults to None, meaning all commits are searched.

        Returns:
            Tuple[Counter[str], Counter[str]]: The count of PRs per contributor and
            reviews per reviewer.
        """
        if self.log_progress:
            print("Retrieving PR information...")
        pr_authors, review_authors = Counter(), Counter()
        cursor = None

        query = """
        query getRepoData($owner: String!, $repo: String!, $cursor: String) {
          repository(owner: $owner, name: $repo) {
            pullRequests(first: 100, after: $cursor) {
              nodes {
                baseRefName
                merged
                author {
                  login
                }
                reviews(first: 100) {  # Assume < 100 reviews, which is reasonable (hopefully!)
                  nodes {
                    author {
                      login
                    }
                  }
                }
              }
              pageInfo {
                hasNextPage
                endCursor
              }
            }
          }
        }
        """

        pages_traversed = 0
        while True:
            variables = {"owner": self.owner, "repo": self.repo, "cursor": cursor}
            data = self._run_github_graphql_query(query, variables=variables)
            pages_traversed += 1

            try:
                prs = data["data"]["repository"]["pullRequests"]
                for pr in prs["nodes"]:
                    base_branch = pr.get("baseRefName")
                    if base_branch != "master":
                        continue  # Skip PRs not to master

                    author = pr["author"]["login"] if pr["author"] else "Unknown Author"
                    if pr["merged"] and author:
                        pr_authors[author] += 1

                    reviews = pr["reviews"]
                    unique_authors = set()
                    for review in reviews["nodes"]:
                        review_author = (
                            review["author"]["login"]
                            if review["author"]
                            else "Unknown Author"
                        )
                        if (
                            review_author != author
                            and review_author not in unique_authors
                        ):
                            unique_authors.add(review_author)
                            review_authors[review_author] += 1

                if self.log_progress:
                    print(
                        "Searched {} PRs ({} reviews) for author information...".format(
                            sum(pr_authors.values()), sum(review_authors.values())
                        )
                    )

                if not prs["pageInfo"]["hasNextPage"] or (
                    page_limit and pages_traversed >= page_limit
                ):
                    break
                cursor = prs["pageInfo"]["endCursor"]
            except KeyError as e:
                print(
                    f"Error accessing data: {e}. Check the structure of the GraphQL response."
                )
                # Print the full response for debugging
                print(json.dumps(data, indent=2))
                return Counter()
            except TypeError as e:
                print(f"Error processing data: {e}. Possibly no commits/PRs/reviews.")
                print(json.dumps(data, indent=2))
                return Counter()

        # Remove ignored users (e.g. automated CI)
        for user in self.IgnoredUsers:
            if user in pr_authors:
                del pr_authors[user]
            if user in review_authors:
                del review_authors[user]

        return pr_authors, review_authors

    def get_existing_committers(self) -> Optional[list[str]]:
        """Get a list of the existing OpenTitan project committers from the
        COMMITTERS_FILE.

        Returns:
            Optional[list[str]]: The list of committers. Returns None if some
            error occurred in the retrieval process.
        """
        if not os.path.exists(COMMITTERS_PATH):
            print("Could not find COMMITTERS file. Did this script move?")
            return None
        if not os.path.isfile(COMMITTERS_PATH):
            print("COMMITTERS file is not a file as expected.")
            return None

        # Get all git revisions in which the COMMITTERS file changed.
        try:
            revision_list = [
                (
                    commit,
                    (commit.tree / COMMITTERS_FILE).data_stream.read().decode("utf-8"),
                )
                for commit in git.Repo().iter_commits(paths=COMMITTERS_PATH)
            ]
        except Exception as e:
            print(f"Error when reading git history of COMMITTERS file: {e}")
            print("Defaulting to use just the current file contents.")
            try:
                with open(COMMITTERS_PATH, "r") as f:
                    revision_list = [("HEAD", f.read())]
            except Exception as e2:
                print(f"Error when reading the COMMITTERS file: {e2}")
                return None

        # For each revision, parse the set of committers. The list of
        # historical committers is then the union of all these sets.
        committers = set()
        for commit, contents in revision_list:
            try:
                committer_list = contents.strip().split("Committer list:")[-1]
                entries = [c[1:].strip() for c in committer_list.splitlines()[1:]]
                for entry in entries:
                    github_id = entry.split(" ")[-1]
                    if not github_id.startswith("(") or not github_id.endswith(")"):
                        print("Warning: skipping unknown ID in COMMITTERS file:")
                        print(f"  {entry}")
                        continue
                    github_id = github_id[1:-1]
                    committers.add(github_id)
            except Exception as e:
                print(f"Error parsing COMMITTERS at revision {commit}: {e}.")
                print("Skipping revision...")
                continue

        return sorted(list(committers))

    def calculate_stats(
        self,
        page_limit: Optional[int] = None,
    ) -> int:
        """Calculate committer, contributor and reviewer statistics for the OpenTitan
        repository. Will output the results to stdout.

        Args:
            page_limit (Optional[int], optional): The number of pages to limit each
            request to. Intended to be used for testing purposes only. Defaults to
            None, meaning no page limits (fetch all the data).

        Returns:
            int: Return code (0 = Ok).
        """
        commit_data = self.get_commit_authors(page_limit=page_limit)
        if commit_data is None:
            print("Error: No commit author data found in response to query.")
            return -1
        pr_data, review_data = self.get_pr_and_review_authors(page_limit=page_limit)
        if pr_data is None:
            print("Error: No PR author data found in response to query.")
            return -1
        elif review_data is None:
            print("Error: No Reviewer data found in response to query.")
            return -1

        # Save the result of the calculation, overwriting any previous results
        self.commit_data = commit_data
        self.pr_data = pr_data
        self.review_data = review_data

        return 0

    def _display_as_table(
        headers: Iterable[str], data: Iterable[Iterable[int]]
    ) -> None:
        """Display the generated contributor statistics as a table.

        Args:
            headers (Iterable[str]): The table column headers to use.
            data (Iterable[Iterable[int]]): The sorted table data, row-by-row.
        """
        print(
            "\nContributors sorted by authored commits, then merged PRs,",
            "then reviewed PRs.\n",
            tabulate(
                data,
                headers,
                tablefmt="pretty",
            ),
        )

    def _display_as_json(fields: Iterable[str], data: Iterable[Iterable[int]]) -> None:
        """Display the generated contributor statistics as JSON output.

        Args:
            fields (Iterable[str]): The JSON field names to use per-entity
            (analogous to table column headers).
            data (Iterable[Iterable[int]]): The sorted entity data, one-by-one.
        """
        # TODO: refactor to make available as a public API that returns the
        # JSON for easier integration into other scripts.
        print(
            json.dumps(
                {
                    entry[0]: {fields[i]: entry[i] for i in range(1, len(entry))}
                    for entry in data
                }
            )
        )

    def _display_as_html(
        headers: Iterable[str], data: Iterable[Iterable[int]], display: bool
    ) -> None:
        """Display the generated contributor statistics as basic HTML.

        Args:
            headers (Iterable[str]): The table column headers to use.
            data (Iterable[Iterable[int]]): The sorted table data, row-by-row.
            display (bool): Whether to open write the HTML, and then display it
            by opening the user's default web browser, or not (just write the
            HTML source to stdout).
        """
        # Format HTML for table headers
        header_html = "                <tr>\n"
        for col in headers:
            header_html += " " * 20 + f'<th align="center">{col}</th>\n'
        header_html += "                </tr>"
        # Format HTML for table rows
        row_html = ""
        for row in data:
            row_html += " " * 16 + "<tr>\n"
            for item in row:
                row_html += " " * 20 + f'<td align = "center">{item}</td>\n'
            row_html += " " * 16 + "</tr>\n"

        # Construct entire table HTML
        table_css = """
    <style>
        table {
            table-layout: auto;
            text-align: center;
            vertical-align: middle;
            width: 90%;
            font-family: arials, sans-serif;
        }
        tr:nth-child(even) {
            background-color: #EEEEEE;
        }
        th, td {
            border: 1px solid #EEEEEE;
        }
    </style>
        """
        table_html = f"""
<html>
    <head></head>
    {table_css.strip()}
    <body>
        <table>
            <thead>
                {header_html.strip()}
            </thead>
            <tbody>
                {row_html.strip()}
            </tbody>
        </table>
    </body>
</html>
        """

        table_html = table_html.strip()
        if not display:
            print(table_html)
            return

        # Write to a pre-determined file rather than a temporary file due to
        # potential compartmentalisation issues with browsers on some OSs.
        with open(HTML_OUTPUT_PATH, "w+") as f:
            f.write(table_html)
        webbrowser.open(f"file://{HTML_OUTPUT_PATH}")

    def display_stats(self, filtered: list[str], format: OutputFormat) -> int:
        """Display the most recently calculated contributor statistics for the
        configured repository. Requires `calculate_stats` to have been called
        at least once previously.

        Args:
            filter (list[str]): A list of entries to filter out of the results,
            so that these entries are not displayed.
            format (OutputFormat): The format to display the results using.

        Returns:
            int: Return code (0 = Ok).
        """
        if self.commit_data is None or self.pr_data is None or self.review_data is None:
            print(
                "Error: cannot display stats unless `calculate_stats` previously",
                "completed successfully.\nThere are no stats to display.",
            )
            return -1

        contributors = (
            set(self.commit_data.keys())
            | set(self.pr_data.keys())
            | set(self.review_data.keys())
        )
        if filtered:
            contributors.difference_update(set(filtered))

        headers = ("Account name", "Commits", "Merged PRs", "PRs Reviewed")
        table = []
        for account in contributors:
            commits = self.commit_data.get(account, 0)
            prs = self.pr_data.get(account, 0)
            reviews = self.review_data.get(account, 0)
            table.append((account, commits, prs, reviews))

        # Sort by commits, then merged PRs, then reviewed PRs.
        table_rows = sorted(table, key=lambda a: tuple(a[1:]), reverse=True)
        for entry in table_rows:
            # Move the "Unknown Author" entry for deleted users to the end
            if entry[0] == "Unknown Author":
                table_rows.remove(entry)
                table_rows.append(entry)
                break

        match format:
            case self.OutputFormat.Table:
                CommitterStatsReporter._display_as_table(headers, table_rows)
            case self.OutputFormat.Json:
                CommitterStatsReporter._display_as_json(headers, table_rows)
            case self.OutputFormat.HtmlDisplay | self.OutputFormat.HtmlOutput:
                CommitterStatsReporter._display_as_html(
                    headers, table_rows, format == self.OutputFormat.HtmlDisplay
                )
            case other_format:
                print(f"Unknown output `format`: {other_format}")
                return -1

        return 0


def main(
    repo_url: str,
    github_token: str,
    filter: bool,
    format: CommitterStatsReporter.OutputFormat,
    log_progress: bool,
    page_limit: Optional[int] = None,
) -> int:
    """The main body of the committer stats script, initialising a reporter
    for the OpenTitan repo with authentication, and then calculating and
    displaying the results.

    Args:
        repo_url (str): The URL of the GitHub repository to query.
        github_token (str): The Github Personal Access Token (PAT) to use for
        API authorization.
        filter (bool): Whether to filter the results to exclude contributors
        that are already in the current `COMMITTERS_FILE`.
        format (CommitterStatsReporter.OutputFormat): Output display format.
        log_progress (bool): Whether to log progress in computing stats or not.
        page_limit (Optional[int], optional): The number of pages to limit each
        request to. Intended to be used for testing purposes only. Defaults to
        None, meaning no page limits (fetch all the data).

    Returns:
        int: Return code (0 = ok).
    """
    try:
        owner, repo = repo_url.split("/")[-2:]
    except ValueError:
        print("Invalid GitHub repository URL format.")
        return -1

    stats = CommitterStatsReporter(owner, repo, github_token, log_progress=log_progress)

    if filter:
        filtered_names = stats.get_existing_committers()
        if filtered_names is None:
            print("Contributor results will not be filtered due to an error.")
            filtered_names = []
        else:
            print(f"Excluding existing committers: {', '.join(filtered_names)}")
    else:
        filtered_names = []

    res = stats.calculate_stats(page_limit=page_limit)
    if res != 0:
        return res

    res = stats.display_stats(filtered_names, format)
    if res != 0:
        return res
    return 0


if __name__ == "__main__":
    import argparse

    # Collect command-line arguments
    desc = "Collect and display contributor statistics for the OpenTitan repo"
    parser = argparse.ArgumentParser(description=desc)

    parser.add_argument(
        "-l",
        "--log-progress",
        action="store_true",
        help="Display progress logs for paginated queries of the repo.",
    )
    parser.add_argument(
        "-p",
        "--pages",
        type=int,
        default=None,
        help=(
            "The number of pages (100 items each) to limit requests to. "
            "Used for testing only."
        ),
    )
    parser.add_argument(
        "-f",
        "--filter",
        action="store_true",
        help="Filter for only contributors not in the current COMMITTERS file.",
    )
    parser.add_argument(
        "-F",
        "--format",
        type=CommitterStatsReporter.OutputFormat,
        default=CommitterStatsReporter.OutputFormat.Table,
        choices=list(CommitterStatsReporter.OutputFormat),
        help="The output contributor stats report format.",
    )

    args = parser.parse_args()

    # Get personal access token from environment variable
    github_token = os.environ.get("GH_GRAPHQL_API_PAT")
    if not github_token:
        print("Error: GH_GRAPHQL_API_PAT environment variable not set.")
        sys.exit(-1)

    sys.exit(
        main(
            OT_REPO_URL,
            github_token,
            args.filter,
            args.format,
            args.log_progress,
            args.pages,
        )
    )
