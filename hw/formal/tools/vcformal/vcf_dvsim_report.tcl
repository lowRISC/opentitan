# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

#####################################################
##   vcf_dvsim_report
#####################################################

proc vcf_dvsim_report { } {
    echo "ID, Type, Status, Property Name, Vacuity, Depth, Engine, Elapsed Time (sec.), Solve Time (sec.)"
    set props [get_props -usage {assert}]
    foreach_in_collection prop_item $props {
	set prop_id      [get_attribute $prop_item id]
	set prop_name    [get_attribute $prop_item name]
	set prop_status  [get_attribute $prop_item status]
	set prop_vacuity [get_attribute $prop_item vacuity]
	set prop_depth   [get_attribute $prop_item trace_depth]
	if { $prop_depth < 0 } { set prop_depth 0 }
	set prop_engine  [get_attribute $prop_item engine]
	set prop_eltime  [get_attribute $prop_item elapsed_time]
	set prop_svtime  [get_attribute $prop_item solve_time]
	echo "${prop_id},assert,${prop_status},${prop_name},${prop_vacuity},${prop_depth},${prop_engine},${prop_eltime},${prop_svtime}"
    }
    set props [get_props -usage {cover}]
    foreach_in_collection prop_item $props {
	set prop_id      [get_attribute $prop_item id]
	set prop_name    [get_attribute $prop_item name]
	set prop_status  [get_attribute $prop_item status]
	set prop_depth   [get_attribute $prop_item trace_depth]
	if { $prop_depth < 0 } { set prop_depth 0 }
	set prop_engine  [get_attribute $prop_item engine]
	set prop_eltime  [get_attribute $prop_item elapsed_time]
	set prop_svtime  [get_attribute $prop_item solve_time]
	echo "${prop_id},cover,${prop_status},${prop_name},,${prop_depth},${prop_engine},${prop_eltime},${prop_svtime}"
    }
    set props [get_props -usage {assume}]
    foreach_in_collection prop_item $props {
	set prop_id      [get_attribute $prop_item id]
	set prop_name    [get_attribute $prop_item name]
	set prop_status  [get_attribute $prop_item status]
	set prop_vacuity [get_attribute $prop_item vacuity]
	echo "${prop_id},assume,${prop_status},${prop_name},${prop_vacuity},,,,"
    }
}
