# Theory of Operation

The following pseudo-code illustrates the range check logic, incorporating range priorities and access control rules.
The default system behavior is to deny access unless explicitly allowed by the range configuration.
The incoming address is compared against each enabled range register, and access control decisions are made based on matching and permissions.
The priority order (a lower range slot has a higher priority) of the ranges ensures that higher-priority ranges override lower-priority ones when a conflict occurs (i.e., if more than one range matches the incoming request).

```
def range_check_access(address, access_type):
  access_granted = False            # Default: access is denied
  for i = 0 to (num_ranges - 1):    # Iterate through ranges, starting from the highest priority
    if range[i].enabled:            # Only process enabled ranges
      # Address matching based on base/limit
      if (range[i].base >= address) and (address < range[i].limit):
        range_match = True
      else:
        range_match = False

      # If address matches within this range, check permissions
      if range_match:
        if access_type == EXECUTE and range[i].execute and access_role in range[i].read_perm:
	  access_granted == True
        else if access_type == READ and range[i].read and access_role in range[i].read_perm:
          access_granted = True
        else if access_type == WRITE and range[i].write and access_role in range[i].write_perm:
          access_granted = True
        else:
          access_granted = False   # No matching permissions
        # Stop after the first match (highest-priority range matched)
        break

  # Return the final access decision
  if access_granted:
    return ACCESS_GRANTED
  else:
    return ACCESS_DENIED
```
