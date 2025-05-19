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

import json
import os
import sys
import requests
from collections import Counter
from typing import Optional, Dict, Tuple, Any


# OpenTitan main repo URL
OT_REPO_URL = "https://github.com/lowRISC/opentitan"

# GraphQL endpoint / query for commits, PRs, and reviews
GH_GRAPHQL_API_ENDPOINT = "https://api.github.com/graphql"


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

        response = requests.post(GH_GRAPHQL_API_ENDPOINT, json=payload, headers=headers)
        response.raise_for_status()

        return response.json()

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

    def display_stats(self) -> int:
        """Display the most recently calculated contributor statistics for the
        configured repository. Requires `calculate_stats` to have been called
        at least once previously.


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
            print(f"- {author}: {count}")

        print("\nPull Request Counts per Contributor:")
        for contributor, count in self.pr_data.most_common():
            print(f"- {contributor}: {count}")

        print("\nReview Counts per Reviewer:")
        for reviewer, count in self.review_data.most_common():
            print(f"- {reviewer}: {count}")

        return 0


def main(
    repo_url: str,
    github_token: str,
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
    res = stats.calculate_stats(page_limit=page_limit)
    if res != 0:
        return res

    res = stats.display_stats()
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

    args = parser.parse_args()

    # Get personal access token from environment variable
    github_token = os.environ.get("GH_GRAPHQL_API_PAT")
    if not github_token:
        print("Error: GH_GRAPHQL_API_PAT environment variable not set.")
        sys.exit(-1)

    sys.exit(main(OT_REPO_URL, github_token, args.log_progress, args.pages))
