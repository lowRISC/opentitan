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
#   You can use `--filter` to filter existing committers, to assist in finding
#   potential candidates for future committers.

import json
import os
import sys
import requests
import time
from collections import Counter
from pathlib import Path
from typing import Optional, Dict, Tuple, Any


# OpenTitan main repo URL
OT_REPO_URL = "https://github.com/lowRISC/opentitan"

# GraphQL endpoint / query for commits, PRs, and reviews
GH_GRAPHQL_API_ENDPOINT = "https://api.github.com/graphql"

# The location of the top of the repository from this file
REPO_TOP = Path(__file__).parents[3]

# The location of the COMMITTERS file within the repo
COMMITTERS_FILE = "COMMITTERS"
COMMITERS_PATH = REPO_TOP / COMMITTERS_FILE


class CommitterStatsReporter:

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
                    for review in reviews["nodes"]:
                        review_author = (
                            review["author"]["login"]
                            if review["author"]
                            else "Unknown Author"
                        )
                        if review_author:
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
        if not os.path.exists(COMMITERS_PATH):
            print("Could not find COMMITTERS file. Did this script move?")
            return None
        if not os.path.isfile(COMMITERS_PATH):
            print("COMMITTERS file is not a file as expected.")
            return None

        try:
            committers = []
            with open(COMMITERS_PATH, "r") as f:
                # Very hard-coded parsing logic based on the COMMITTER file format
                committer_list = f.read().strip().split("Committer list:")[-1]
                entries = [c[1:].strip() for c in committer_list.splitlines()[1:]]
                for entry in entries:
                    github_id = entry.split(" ")[-1]
                    if not github_id.startswith("(") or not github_id.endswith(")"):
                        print("Warning: skipping unknown ID in COMMITTERS file:")
                        print(f"  {entry}")
                        continue
                    github_id = github_id[1:-1]
                    committers.append(github_id)

            return committers
        except Exception as e:
            print(f"Error when reading the COMMITTERS file: {e}")
            return None

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

    def display_stats(self, filtered: list[str]) -> int:
        """Display the most recently calculated contributor statistics for the
        configured repository. Requires `calculate_stats` to have been called
        at least once previously.

        Args:
            filter (list[str]): A list of entries to filter out of the results,
            so that these entries are not displayed.

        Returns:
            int: Return code (0 = Ok).
        """
        if self.commit_data is None or self.pr_data is None or self.review_data is None:
            print(
                "Error: cannot display stats unless `calculate_stats` previously",
                "completed successfully.\nThere are no stats to display.",
            )
            return -1

        print("\nCommit Counts per Author:")
        for author, count in self.commit_data.most_common():
            if author in filtered:
                continue
            print(f"- {author}: {count}")

        print("\nPull Request Counts per Contributor:")
        for contributor, count in self.pr_data.most_common():
            if contributor in filtered:
                continue
            print(f"- {contributor}: {count}")

        print("\nReview Counts per Reviewer:")
        for reviewer, count in self.review_data.most_common():
            if reviewer in filtered:
                continue
            print(f"- {reviewer}: {count}")

        return 0


def main(
    repo_url: str,
    github_token: str,
    filter: bool,
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

    res = stats.display_stats(filtered_names)
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

    args = parser.parse_args()

    # Get personal access token from environment variable
    github_token = os.environ.get("GH_GRAPHQL_API_PAT")
    if not github_token:
        print("Error: GH_GRAPHQL_API_PAT environment variable not set.")
        sys.exit(-1)

    sys.exit(
        main(OT_REPO_URL, github_token, args.filter, args.log_progress, args.pages)
    )
