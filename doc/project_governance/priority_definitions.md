---
title: Generalized Priority Definitions
---

## Definitions

The priorities described below draw inspiration from the [Google Issue Tracker](https://developers.google.com/issue-tracker/concepts/issues#priority) and have been completely reformulated to fit the OpenTitan setting.
The following definitions are used:

*  **Work streams**: OpenTitan sub-projects which typically have their own associated working group, e.g.: discrete chip, integrated IP.
*  **Milestones**: Milestones (M1, M2 etc)  associated with a specific work stream.
*  **Core function**: Core function of OpenTitan in any of the relevant engineering domains (HW, SW, security).

### Priority Definitions Table


| Issue Priority | Description
| ---------------|------------
| **P0 - Blocking** | An issue that requires immediate resolution. Examples include top-of-tree CI outages or merge skew causing compilation simulation or synthesis breakages.
| **P1 - High** | An issue requiring quick resolution since it significantly impacts a large percentage of functionality or maintainers; existing workarounds are only partial or exceedingly painful. The issue impacts a core function, and/or fundamentally impedes progress towards target milestones on any of the work streams.
| **P2 - Default** | An issue that needs to be resolved within a reasonable amount of time. This could be:
| | (a) an issue that would have a higher priority, but has a reasonable workaround,
| | (b) an issue that impacts a large percentage of maintainers and is linked with a core function,
| | (c) an issue that needs to be addressed to reach the next milestone on a given work stream.
| | This is the default priority level.
| **P3 - Best effort** | An issue that should be resolved on a best effort basis. Such an issue is relevant to core functions of OpenTitan, but does not impede progress towards target milestones on a given work stream or else has a reasonable workaround
| **P4 - Deferrable** | An issue that should be resolved eventually. Such an issue is not relevant to core functions or upcoming milestones on any of the work streams; or it only addresses cosmetic aspects of the underlying subject.
