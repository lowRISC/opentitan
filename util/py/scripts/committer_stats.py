#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script uses the GraphQL GitHub API to compute committer statistics for
# the OpenTitan project.
#
# Usage:
#  - set the following environment variables:
#    - "GH_GRAPHQL_API_PAT": this is a personal access token generate for your
#       GitHub account that will enable this script to use the GitHub GraphQL
#       API. Follow the instructions here on how to create one:
#       https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens
# - run this script with no parameters

import json
import os

import requests

# OpenTitan main repo URL
OT_REPO_URL = "https://github.com/lowRISC/opentitan"

# GraphQL endpoint / query for commits, PRs, and reviews
GH_GRAPHQL_API_ENDPOINT = 'https://api.github.com/graphql'
GH_GRAPHQL_API_QUERY = """
query getRepoData($owner: String!, $repo: String!) {
      repository(owner: $owner, name: $repo) {
        commits: defaultBranchRef {
          target {
            ... on Commit {
              history {
                edges {
                  node {
                    author {
                      user {
                        login
                      }
                    }
                  }
                }
              }
            }
          }
        }
        pullRequests(states: [CLOSED], last: 100) { # Added 'last: 100' for pagination
          nodes {
            author {
              login
            }
            reviews(first: 100) {  # Limit to 100 reviews per PR.  Use pagination if needed.
              nodes {
                author {
                  login
                }
              }
            }
          }
        }
      }
    }
"""


def get_github_data_graphql(repo_url, github_token=None):
    """
    Fetches commit, pull request, and review data for a GitHub repository using the GraphQL API.

    Args:
        repo_url (str): The URL of the GitHub repository (e.g., "https://github.com/owner/repo").
        github_token (str, optional): Your GitHub personal access token. Defaults to None.

    Returns:
        tuple: A tuple containing dictionaries for commit, PR, and review counts per author.
    """
    try:
        owner, repo = repo_url.split('/')[-2:]
    except ValueError:
        print("Invalid GitHub repository URL format.")
        return None, None, None

    headers = {}
    if github_token:
        headers[
            'Authorization'] = f'bearer {github_token}'  # Note the 'bearer' scheme
    headers['Content-Type'] = 'application/json'

    commit_counts = {}
    pr_counts = {}
    review_counts = {}

    variables = {
        'owner': owner,
        'repo': repo,
    }
    payload = {
        'query': GH_GRAPHQL_API_QUERY,
        'variables': variables,
    }

    response = requests.post(GH_GRAPHQL_API_ENDPOINT,
                             json=payload,
                             headers=headers)
    response.raise_for_status()
    data = response.json()

    # Process the data
    try:
        commits = data['data']['repository']['commits']['target']['history'][
            'edges']
        for commit in commits:
            author = commit['node']['author']['user']['login'] if commit[
                'node']['author']['user'] else "Unknown Author"
            commit_counts[author] = commit_counts.get(author, 0) + 1

        pull_requests = data['data']['repository']['pullRequests']['nodes']
        for pr in pull_requests:
            pr_author = pr['author']['login']
            pr_counts[pr_author] = pr_counts.get(pr_author, 0) + 1
            if pr['reviews']:  # Check if reviews exist
                for review in pr['reviews']['nodes']:
                    reviewer = review['author']['login']
                    review_counts[reviewer] = review_counts.get(reviewer,
                                                                0) + 1
    except KeyError as e:
        print(
            f"Error accessing data: {e}.  Check the structure of the GraphQL response."
        )
        print(json.dumps(data,
                         indent=2))  # Print the full response for debugging
        return None, None, None
    except TypeError as e:
        print(f"Error processing data: {e}.  Possibly no commits/PRs/reviews.")
        print(json.dumps(data, indent=2))
        return {}, {}, {}  # Return empty dicts to avoid crashing

    return commit_counts, pr_counts, review_counts


def main():
    # Get personal access token from environment variable
    github_token = os.environ.get('GH_GRAPHQL_API_PAT')
    if not github_token:
        print("Error: GH_GRAPHQL_API_PAT environment variable not set.")
        return

    commit_data, pr_data, review_data = get_github_data_graphql(
        OT_REPO_URL, github_token)

    if commit_data is not None and pr_data is not None and review_data is not None:
        print("\nCommit Counts per Author:")
        for author, count in commit_data.items():
            print(f"- {author}: {count}")

        print("\nPull Request Counts per Contributor:")
        for contributor, count in pr_data.items():
            print(f"- {contributor}: {count}")

        print("\nReview Counts per Reviewer:")
        for reviewer, count in review_data.items():
            print(f"- {reviewer}: {count}")
    else:
        print("Failed to retrieve data.")


if __name__ == "__main__":
    main()
