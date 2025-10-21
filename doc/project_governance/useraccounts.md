# OpenTitan user accounts

## OpenTitan accounts
OpenTitan accounts (an opentitan.org google account with associated project permisisons) are required for most OpenTitan activity.
This includes:
- **Contribution**.  Only OpenTitan accounts can be used to contribute code on GitHub
- **Mailing Lists**.  Only OpenTitan accounts can be used on mailing lists
- **Groups**.  Governing Board, Technical Committee and Working Group memberships can only use OpenTitan accounts

This page outlines how accounts are obtained and managed.

## Contributor License Agreement (CLA)

All contributions to the project are under the terms of the [Contributor License Agreement](https://github.com/lowRISC/opentitan/blob/master/CLA) (CLA) which is referenced on every commit.
This grants patent and copyright licenses to the project so that any submissions can legally be used by OpenTitan and downstream users.
Copyright remains unchanged.

More than 200 individuals from more than 25 organizations and more than 20 non-organizational individuals have contributed to OpenTitan to date.
If all of them would add their own attribution or copyright notices, that would clutter the code base.
Copyright is therefore indicated in OpenTitan files by a generic header:

`Copyright lowRISC contributors (OpenTitan project).`

Detailed and up-to-date attribution for all contributions is available via the Git version control system:
- `git shortlog --author "<your name>"` lists all contributions under your name
- `git shortlog --author "<organization's domain>"` lists all contributions by an organization.
- `git shortlog -- <path>` lists all contributors for a file or directory tree

## Project Participants

Submitters must be legally entitled to grant patent or copyright licenses for their own work.
There are different categories of submitter who use different mechanisms for this.

- **Partner Individuals** are individuals working for a Project Partner and designated by that Partner.
- **Individual Collaborators** are individuals who are not working for any organisation.
- **Non-partner individuals** exist for the unusual case of individuals who are working for an organisation which is not a Project Partner.

*lowRISC reserves the right to refuse, or revoke, Project Participant status to any individual where, in the opinion of lowRISC C.I.C. (following consultation with the respective Project Partner in the case of Partner Individuals),*
*the actions, inactions, conduct or connections of the Project Participant have harmed or risk harming the perception or reputation of lowRISC, the OpenTitan Project and/or any Project Partner.*

*For non-partner individuals and individual collaborators, the decision on admission shall be made in the best interests of the Project as a whole and in keeping with lowRISC's and the Project's open source mission.*
*Any decision not to admit a person must be based on objective factors (such as legal or reputational risk to the Project, non-compliance with laws, costs, or scalability)*
*and not discrimination against the individual or any institution associated with them.*

### Partner Individuals

Partner Individuals are those working for an OpenTitan Project Partner and designated by that Project Partner as one of its contributors to the OpenTitan project.
No separate legal agreement beyond the partner agreement is required.

Partners may identify individuals as Partner Individuals by requesting an OpenTitan account (see below).
A number of OpenTitan accounts are available according to the Partnership agreement.
By identifying an individual as a Partner Individual, the Partner authorises them to agree to the terms in the OpenTitan CLA when making contributions.

If a Partner Individual leaves the employment of a Project Partner, the Project Partner must notify lowRISC C.I.C. promptly so that they can be removed from the Project.

### Individual Collaborators

Individual Collaborators are individuals who wish to make a significant contribution to the OpenTitan project, either on their own or as part of a team.
They should not be associated with any company.
An individual can be 'associated with' a company or other institution by being an employee, consultant or director of the institution, or because they are primarily funded by an institution.

They will need to sign an Individual Collaborator license agreement to gain access to OpenTitan.

### Non-Partner Individuals

In unusual cases, participants may be associated with an organisation which is not an OpenTitan Project Partner.
As the individuals are assigning licenses to the project, the organisation will need to sign a [corporate contributor license agreement](./corporate_cla.txt).

## Account Management

### Requesting a partner individual account
User accounts are available through partner membership.
Accounts are requested from get-involved@opentitan.org.
If you have more people wishing to get involved than the free entitlement from your partner membership, further user accounts can be purchased.

The limit on OpenTitan accounts according to your partnership level is applied to **open** accounts.
If an account is not needed, it can be closed by contacting get-involved@opentitan.org and the account entitlement reused.

### Requesting other accounts
Individual Collaborators should be proposed by lowRISC or a Project Partner, a decision by the Governing Board and approval by lowRISC after an Individual Collaborator agreement is signed.

Non-Partner individuals should be discussed directly with lowRISC.

### Using an OpenTitan account
All communications using your OpenTitan account are as part of the OpenTitan community.
Please be aware of, and comply with, the [code of conduct](./code_of_conduct.md).

OpenTitan accounts are for individuals, and should not be shared between individuals, even within the same Partner organisation.

The OpenTitan account is intended for managing communications within OpenTitan.
The associated storage ("OpenTitan workspaces") are not intended for long-term storage and there is no guarantee that data will not be deleted.
- OpenTitan workspaces should not be used as general storage space to store non-OpenTitan material.
- Company confidential material and non-OpenTitan IP should not be stored in OpenTitan workspaces.
- lowRISC, as stewards of OpenTitan, are not responsible for management and backup of OpenTitan workspaces.
- If OpenTitan accounts are closed, associated workspace data is deleted.

### Maintenance of OpenTitan accounts
If you no longer need your OpenTitan account, please notify get-involved@opentitan.org and the account can be closed.

If a Partner Individual leaves the employment of a Project Partner, the Project Partner must notify lowRISC C.I.C. promptly so that they can be removed from the project.

If an OpenTitan account is not being used, it will eventually be closed, following the process below:
- OpenTitan account usage will be monitored quarterly
- Using an account is considered any of the following:
  - Signing in to the account
  - Sending a slack message
  - Any GitHub activity using the account
- If an account has not been used for **6 months** it is considered **inactive**
- If an account is **inactive** the owner will be sent a warning that the account may be deleted
- If there is no response and the account remains **inactive** the account will be **closed** after **one month**
- When this happens, all data stored in the associated personal Google workspace (e.g. MyDrive, Calendar, Gmail, etc) is deleted, with no backup maintained
