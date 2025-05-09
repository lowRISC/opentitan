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
import time
from collections import Counter
from typing import Optional, Dict, Tuple, Any

# Flag to log progress in generating info
LOG_PROGRESS = False

# OpenTitan main repo URL
OT_REPO_URL = "https://github.com/lowRISC/opentitan"

# GraphQL endpoint / query for commits, PRs, and reviews
GH_GRAPHQL_API_ENDPOINT = "https://api.github.com/graphql"


def run_github_graphql_query(
    query: str,
    variables: Optional[Dict[str, Any]] = None,
    github_token: Optional[str] = None,
) -> Dict[str, Any]:
    """Run a query on the Github GraphQL API.

    Args:
        query (str): The GraphQL query to post.
        variables (Optional[Dict[str, Any]], optional): The variables to insert
        into the query. Defaults to None.
        github_token (Optional[str], optional): The Github Personal Access Token
        (PAT) to use for authorization. Defaults to None.

    Returns:
        Dict[str, Any]: The JSON response from the Github API.
    """
    headers = {"Content-Type": "application/json"}
    if github_token is not None:
        # Note that we use the 'bearer' scheme
        headers["Authorization"] = f"Bearer {github_token}"

    payload = {"query": query}
    if variables is not None:
        payload["variables"] = variables

    sleep_time = None
    while True:
        try:
            response = requests.post(
                GH_GRAPHQL_API_ENDPOINT, json=payload, headers=headers
            )
            if sleep_time is not None:
                time.sleep(sleep_time)
            response.raise_for_status()
        except requests.exceptions.ConnectTimeout:
            if sleep_time is None:
                sleep_time = 1
            else:
                sleep_time *= 2
                print(
                    "Unable to connect to Github API. Retrying with a",
                    f"wait of {sleep_time} seconds...",
                )
            continue


        # Check status code
        if response.status_code == 403 and "X-RateLimit-Remaining" in response.headers:
            # If we hit a wait limit, sleep for the suggested time.
            remaining_reqs = int(response.headers["X-RateLimit-Remaining"])
            reset = int(response.headers.get("X-RateLimit-Reset", 0))
            if remaining_reqs == 0:
                wait_time = max(reset - time.time(), 5)
                if LOG_PROGRESS:
                    print(
                        f"Rate limit exceeded - sleeping for {int(wait_time)}",
                        "seconds before retrying...",
                    )
                time.sleep(wait_time)
                continue
        elif response.status_code != 200:  # HTTP OK
            print(f"Query failed with code {response.status_code}: {response.text}")
            sys.exit(-1)

        # Check for GraphQL errors
        data = response.json()
        if "errors" in data:
            print(f"GraphQL error: {data['errors']}")
        return data


def get_commit_authors(
    owner: str,
    repo: str,
    github_token: Optional[str] = None,
    page_limit: Optional[int] = None,
) -> Counter[str]:
    """Get information about the authors of commits in a Github repository.

    Args:
        owner (str): The owner of the Github repository to query.
        repo (str): The name of the Github repository to query.
        github_token (Optional[str], optional): The Github Personal Access Token
        (PAT) to use for authorization. Defaults to None.
        page_limit (Optional[int], optional): A limit for the number of (100-item)
        pages to query. Will then return the first N pages, which is useful for
        testing. Defaults to None, meaning all commits are searched.

    Returns:
        Counter[str]: The count of commits per committer.
    """
    if LOG_PROGRESS:
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
        variables = {"owner": owner, "repo": repo, "cursor": cursor}
        data = run_github_graphql_query(
            query, variables=variables, github_token=github_token
        )
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

            if LOG_PROGRESS:
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

    # Exclude automated CI
    if "github-actions" in authors:
        del authors["github-actions"]

    return authors


def get_pr_and_review_authors(
    owner: str,
    repo: str,
    github_token: Optional[str] = None,
    page_limit: Optional[int] = None,
) -> Tuple[Counter[str], Counter[str]]:
    """Get information about the authors of PRs and reviews on those PRs in a
    Github repository.

    Args:
        owner (str): The owner of the Github repository to query.
        repo (str): The name of the Github repository to query.
        github_token (Optional[str], optional): The Github Personal Access Token
        (PAT) to use for authorization. Defaults to None.
        page_limit (Optional[int], optional): A limit for the number of (100-item)
        pages to query. Will then return the first N pages, which is useful for
        testing. Defaults to None, meaning all commits are searched.

    Returns:
        Tuple[Counter[str], Counter[str]]: The count of PRs per contributor and
        reviews per reviewer.
    """
    if LOG_PROGRESS:
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
        variables = {"owner": owner, "repo": repo, "cursor": cursor}
        data = run_github_graphql_query(
            query, variables=variables, github_token=github_token
        )
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

            if LOG_PROGRESS:
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

    # Exclude automated CI
    if "github-actions" in pr_authors:
        del pr_authors["github-actions"]
    if "github-actions" in review_authors:
        del review_authors["github-actions"]

    return pr_authors, review_authors


def main(github_token: str, page_limit: Optional[int] = None) -> int:
    """Calculate committer, contributor and reviewer statistics for the OpenTitan
    repository. Will output the results to stdout.

    Args:
        github_token (Optional[str], optional): The Github Personal Access Token
        (PAT) to use for authorization. Defaults to None.
        page_limit (Optional[int], optional): The number of pages to limit each
        request to. Intended to be used for testing purposes only. Defaults to
        None, meaning no page limits (fetch all the data).

    Returns:
        int: Return code (0 = Ok).
    """
    try:
        owner, repo = OT_REPO_URL.split("/")[-2:]
    except ValueError:
        print("Invalid GitHub repository URL format.")
        return -1

    commit_data = get_commit_authors(
        owner, repo, github_token=github_token, page_limit=page_limit
    )
    if commit_data is None:
        print("Error: No commit author data found in response to query.")
        return -1
    pr_data, review_data = get_pr_and_review_authors(
        owner, repo, github_token=github_token, page_limit=page_limit
    )
    if pr_data is None:
        print("Error: No PR author data found in response to query.")
        return -1
    elif review_data is None:
        print("Error: No Reviewer data found in response to query.")
        return -1

    print("\nCommit Counts per Author:")
    for author, count in commit_data.most_common():
        print(f"- {author}: {count}")

    print("\nPull Request Counts per Contributor:")
    for contributor, count in pr_data.most_common():
        print(f"- {contributor}: {count}")

    print("\nReview Counts per Reviewer:")
    for reviewer, count in review_data.most_common():
        print(f"- {reviewer}: {count}")

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

    if args.log_progress:
        LOG_PROGRESS = True

    # Get personal access token from environment variable
    github_token = os.environ.get("GH_GRAPHQL_API_PAT")
    if not github_token:
        print("Error: GH_GRAPHQL_API_PAT environment variable not set.")
        sys.exit(-1)

    sys.exit(main(github_token, args.pages))
