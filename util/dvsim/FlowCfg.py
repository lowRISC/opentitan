# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing a flow configuration object
"""

import datetime
import logging as log
import pprint
from shutil import which

import hjson

from Deploy import *
from utils import *


# Interface class for extensions.
class FlowCfg():
    def __str__(self):
        return pprint.pformat(self.__dict__)

    def __repr__(self):
        return pprint.pformat(self.__dict__)

    def __init__(self, flow_cfg_file, proj_root, args):
        # Options set from command line
        self.items = []
        self.items.extend(args.items)
        self.list_items = []
        self.list_items.extend(args.list)
        self.select_cfgs = []
        self.select_cfgs.extend(args.select_cfgs)
        self.flow_cfg_file = flow_cfg_file
        self.proj_root = proj_root
        self.args = args
        self.scratch_root = args.scratch_root
        self.branch = args.branch
        self.job_prefix = args.job_prefix

        # Options set from hjson cfg.
        self.project = ""
        self.scratch_path = ""

        # Imported cfg files using 'import_cfgs' keyword
        self.imported_cfg_files = []
        self.imported_cfg_files.append(flow_cfg_file)

        # Add exports using 'exports' keyword - these are exported to the child
        # process' environment.
        self.exports = []

        # Add overrides using the overrides keyword - existing attributes
        # are overridden with the override values.
        self.overrides = []

        # List of cfgs if the parsed cfg is a master cfg list
        self.cfgs = []

        # Add a notion of "master" cfg - this is indicated using
        # a special key 'use_cfgs' within the hjson cfg.
        self.is_master_cfg = False

        # For a master cfg, it is the aggregated list of all deploy objects under self.cfgs.
        # For a non-master cfg, it is the list of items slated for dispatch.
        self.deploy = []

        # Timestamp
        self.ts_format_long = args.ts_format_long
        self.timestamp_long = args.timestamp_long
        self.ts_format = args.ts_format
        self.timestamp = args.timestamp

        # Results
        self.errors_seen = False
        self.rel_path = ""
        self.results_title = ""
        self.results_server_prefix = ""
        self.results_server_url_prefix = ""
        self.results_server_cmd = ""
        self.results_server_css_path = ""
        self.results_server_path = ""
        self.results_server_dir = ""
        self.results_server_html = ""
        self.results_server_page = ""
        self.results_summary_server_html = ""
        self.results_summary_server_page = ""

        # Full and summary results in md text.
        self.results_md = ""
        self.results_summary_md = ""

    def __post_init__(self):
        # Run some post init checks
        if not self.is_master_cfg:
            # Check if self.cfgs is a list of exactly 1 item (self)
            if not (len(self.cfgs) == 1 and self.cfgs[0].name == self.name):
                log.error("Parse error!\n%s", self.cfgs)
                sys.exit(1)

    @staticmethod
    def create_instance(flow_cfg_file, proj_root, args):
        '''Create a new instance of this class as with given parameters.
        '''
        return FlowCfg(flow_cfg_file, proj_root, args)

    def kill(self):
        '''kill running processes and jobs gracefully
        '''
        for item in self.deploy:
            item.kill()

    def parse_flow_cfg(self, flow_cfg_file, is_entry_point=True):
        '''
        Parse the flow cfg hjson file. This is a private API used within the
        extended class' __init__ function. This parses the hjson cfg (and
        imports / use cfgs) and builds an initial dictionary.

        This method takes 2 args.
        flow_cfg_file: This is the flow cfg file to be parsed.
        is_entry_point: the cfg file that is passed on the command line is
            the entry point cfg. If the cfg file is a part of an inport_cfgs
            or use_cfgs key, then it is not an entry point.
        '''
        hjson_dict = parse_hjson(flow_cfg_file)

        # Check if this is the master cfg, if this is the entry point cfg file
        if is_entry_point:
            self.is_master_cfg = self.check_if_master_cfg(hjson_dict)

            # If not a master cfg, then register self with self.cfgs
            if self.is_master_cfg is False:
                self.cfgs.append(self)

        # Resolve the raw hjson dict to build this object
        self.resolve_hjson_raw(hjson_dict)

    def _post_parse_flow_cfg(self):
        '''Hook to set some defaults not found in the flow cfg hjson files.
        This function has to be called manually after calling the parse_flow_cfg().
        '''
        if self.rel_path == "":
            self.rel_path = os.path.dirname(self.flow_cfg_file).replace(
                self.proj_root + '/', '')

    def check_if_master_cfg(self, hjson_dict):
        # This is a master cfg only if it has a single key called "use_cfgs"
        # which contains a list of actual flow cfgs.
        hjson_cfg_dict_keys = hjson_dict.keys()
        return ("use_cfgs" in hjson_cfg_dict_keys and \
                type(hjson_dict["use_cfgs"]) is list)

    def resolve_hjson_raw(self, hjson_dict):
        attrs = self.__dict__.keys()
        rm_hjson_dict_keys = []
        import_cfgs = []
        use_cfgs = []
        for key in hjson_dict.keys():
            if key in attrs:
                hjson_dict_val = hjson_dict[key]
                self_val = getattr(self, key)
                scalar_types = {str: [""], int: [0, -1], bool: [False]}

                # Case 1: key value in class and hjson_dict differ - error!
                if type(hjson_dict_val) != type(self_val):
                    log.error("Conflicting key types: \"%s\" {\"%s, \"%s\"}",
                              key,
                              type(hjson_dict_val).__name__,
                              type(self_val).__name__)
                    sys.exit(1)

                # Case 2: key value in class and hjson_dict are strs - set if
                # not already set, else error!
                elif type(hjson_dict_val) in scalar_types.keys():
                    defaults = scalar_types[type(hjson_dict_val)]
                    if self_val == hjson_dict_val:
                        rm_hjson_dict_keys.append(key)
                    elif self_val in defaults and not hjson_dict_val in defaults:
                        setattr(self, key, hjson_dict_val)
                        rm_hjson_dict_keys.append(key)
                    elif not self_val in defaults and not hjson_dict_val in defaults:
                        # check if key exists in command line args, use that, or
                        # throw conflicting error
                        # TODO, may throw the conflicting error but choose one and proceed rather
                        # than exit
                        override_with_args_val = False
                        if hasattr(self.args, key):
                            args_val = getattr(self.args, key)
                            if type(args_val) == str and args_val != "":
                                setattr(self, key, args_val)
                                override_with_args_val = True
                        if not override_with_args_val:
                            log.error(
                                "Conflicting values {\"%s\", \"%s\"} encountered for key \"%s\"",
                                str(self_val), str(hjson_dict_val), key)
                            sys.exit(1)

                # Case 3: key value in class and hjson_dict are lists - merge'em
                elif type(hjson_dict_val) is list and type(self_val) is list:
                    self_val.extend(hjson_dict_val)
                    setattr(self, key, self_val)
                    rm_hjson_dict_keys.append(key)

                # Case 4: unknown issue
                else:
                    log.error(
                        "Type of \"%s\" (%s) in %s appears to be invalid (should be %s)",
                        key,
                        type(hjson_dict_val).__name__, hjson_dict,
                        type(self_val).__name__)
                    sys.exit(1)

            # If key is 'import_cfgs' then add to the list of cfgs to
            # process
            elif key == 'import_cfgs':
                import_cfgs.extend(hjson_dict[key])
                rm_hjson_dict_keys.append(key)

            # If this is a master cfg list and the key is 'use_cfgs'
            elif self.is_master_cfg and key == "use_cfgs":
                use_cfgs.extend(hjson_dict[key])

            # If this is a not master cfg list and the key is 'use_cfgs'
            elif not self.is_master_cfg and key == "use_cfgs":
                # Throw an error and exit
                log.error(
                    "Key \"use_cfgs\" encountered in a non-master cfg file list \"%s\"",
                    self.flow_cfg_file)
                sys.exit(1)

            else:
                # add key-value to class
                setattr(self, key, hjson_dict[key])
                rm_hjson_dict_keys.append(key)

        # Parse imported cfgs
        for cfg_file in import_cfgs:
            if not cfg_file in self.imported_cfg_files:
                self.imported_cfg_files.append(cfg_file)
                # Substitute wildcards in cfg_file files since we need to process
                # them right away.
                cfg_file = subst_wildcards(cfg_file, self.__dict__)
                self.parse_flow_cfg(cfg_file, False)
            else:
                log.error("Cfg file \"%s\" has already been parsed", cfg_file)

        # Parse master cfg files
        if self.is_master_cfg:
            for entry in use_cfgs:
                if type(entry) is str:
                    # Treat this as a file entry
                    # Substitute wildcards in cfg_file files since we need to process
                    # them right away.
                    cfg_file = subst_wildcards(entry,
                                               self.__dict__,
                                               ignore_error=True)
                    self.cfgs.append(
                        self.create_instance(cfg_file, self.proj_root,
                                             self.args))

                elif type(entry) is dict:
                    # Treat this as a cfg expanded in-line
                    temp_cfg_file = self._conv_inline_cfg_to_hjson(entry)
                    if not temp_cfg_file: continue
                    self.cfgs.append(
                        self.create_instance(temp_cfg_file, self.proj_root,
                                             self.args))

                    # Delete the temp_cfg_file once the instance is created
                    try:
                        log.log(VERBOSE, "Deleting temp cfg file:\n%s",
                                temp_cfg_file)
                        os.system("/bin/rm -rf " + temp_cfg_file)
                    except IOError:
                        log.error("Failed to remove temp cfg file:\n%s",
                                  temp_cfg_file)

                else:
                    log.error(
                        "Type of entry \"%s\" in the \"use_cfgs\" key is invalid: %s",
                        entry, str(type(entry)))
                    sys.exit(1)

    def _conv_inline_cfg_to_hjson(self, idict):
        '''Dump a temp hjson file in the scratch space from input dict.
        This method is to be called only by a master cfg'''

        if not self.is_master_cfg:
            log.fatal("This method can only be called by a master cfg")
            sys.exit(1)

        name = idict["name"] if "name" in idict.keys() else None
        if not name:
            log.error(
                "In-line entry in use_cfgs list does not contain " + \
                "a \"name\" key (will be skipped!):\n%s", idict)
            return None

        # Check if temp cfg file already exists
        temp_cfg_file = self.scratch_root + "/." + self.branch + "__" + \
                        name + "_cfg.hjson"

        # Create the file and dump the dict as hjson
        log.log(VERBOSE, "Dumping inline cfg \"%s\" in hjson to:\n%s", name,
                temp_cfg_file)
        try:
            with open(temp_cfg_file, "w") as f:
                f.write(hjson.dumps(idict, for_json=True))
        except Exception as e:
            log.error(
                "Failed to hjson-dump temp cfg file\"%s\" for \"%s\"" + \
                "(will be skipped!) due to:\n%s", temp_cfg_file, name, e)
            return None

        # Return the temp cfg file created
        return temp_cfg_file

    def _process_overrides(self):
        # Look through the dict and find available overrides.
        # If override is available, check if the type of the value for existing
        # and the overridden keys are the same.
        overrides_dict = {}
        if hasattr(self, "overrides"):
            overrides = getattr(self, "overrides")
            if type(overrides) is not list:
                log.error(
                    "The type of key \"overrides\" is %s - it should be a list",
                    type(overrides))
                sys.exit(1)

            # Process override one by one
            for item in overrides:
                if type(item) is dict and set(item.keys()) == set(
                    ["name", "value"]):
                    ov_name = item["name"]
                    ov_value = item["value"]
                    if ov_name not in overrides_dict.keys():
                        overrides_dict[ov_name] = ov_value
                        self._do_override(ov_name, ov_value)
                    else:
                        log.error(
                            "Override for key \"%s\" already exists!\nOld: %s\nNew: %s",
                            ov_name, overrides_dict[ov_name], ov_value)
                        sys.exit(1)
                else:
                    log.error("\"overrides\" is a list of dicts with {\"name\": <name>, " + \
                              "\"value\": <value>} pairs. Found this instead:\n%s",
                              str(item))
                    sys.exit(1)

    def _do_override(self, ov_name, ov_value):
        # Go through self attributes and replace with overrides
        if hasattr(self, ov_name):
            orig_value = getattr(self, ov_name)
            if type(orig_value) == type(ov_value):
                log.debug("Overriding \"%s\" value \"%s\" with \"%s\"",
                          ov_name, orig_value, ov_value)
                setattr(self, ov_name, ov_value)
            else:
                log.error("The type of override value \"%s\" for \"%s\" mismatches " + \
                          "the type of original value \"%s\"",
                          ov_value, ov_name, orig_value)
                sys.exit(1)
        else:
            log.error("Override key \"%s\" not found in the cfg!", ov_name)
            sys.exit(1)

    def _process_exports(self):
        # Convert 'exports' to dict
        exports_dict = {}
        if self.exports != []:
            for item in self.exports:
                if type(item) is dict:
                    exports_dict.update(item)
                elif type(item) is str:
                    [key, value] = item.split(':', 1)
                    if type(key) is not str: key = str(key)
                    if type(value) is not str: value = str(value)
                    exports_dict.update({key.strip(): value.strip()})
                else:
                    log.error("Type error in \"exports\": %s", str(item))
                    sys.exit(1)
        self.exports = exports_dict

    def _purge(self):
        '''Purge the existing scratch areas in preperation for the new run.'''
        return

    def purge(self):
        '''Public facing API for _purge().
        '''
        for item in self.cfgs:
            item._purge()

    def _print_list(self):
        '''Print the list of available items that can be kicked off.
        '''
        return

    def print_list(self):
        '''Public facing API for _print_list().
        '''
        for item in self.cfgs:
            item._print_list()

    # function to prune only selected cfgs to build and run
    # it will return if the object is not a master_cfg or -select_cfgs is empty
    def prune_selected_cfgs(self):
        if not self.is_master_cfg or not self.select_cfgs:
            return
        else:
            remove_cfgs = []
            for item in self.cfgs:
                if item.name not in self.select_cfgs:
                    remove_cfgs.append(item)
            for remove_cfg in remove_cfgs:
                self.cfgs.remove(remove_cfg)

    def _create_deploy_objects(self):
        '''Create deploy objects from items that were passed on for being run.
        The deploy objects for build and run are created from the objects that were
        created from the create_objects() method.
        '''
        return

    def create_deploy_objects(self):
        '''Public facing API for _create_deploy_objects().
        '''
        self.prune_selected_cfgs()
        if self.is_master_cfg:
            self.deploy = []
            for item in self.cfgs:
                item._create_deploy_objects()
                self.deploy.extend(item.deploy)
        else:
            self._create_deploy_objects()

    def deploy_objects(self):
        '''Public facing API for deploying all available objects.'''
        Deploy.deploy(self.deploy)

    def _gen_results(self, fmt="md"):
        '''
        The function is called after the regression has completed. It collates the
        status of all run targets and generates a dict. It parses the testplan and
        maps the generated result to the testplan entries to generate a final table
        (list). It also prints the full list of failures for debug / triage. The
        final result is in markdown format.
        '''
        return

    def gen_results(self):
        '''Public facing API for _gen_results().
        '''
        results = []
        for item in self.cfgs:
            result = item._gen_results()
            log.info("[results]: [%s]:\n%s\n\n", item.name, result)
            results.append(result)
            self.errors_seen |= item.errors_seen

        if self.is_master_cfg: self.gen_results_summary()
        self.gen_email_html_summary()

    def gen_results_summary(self):
        '''Public facing API to generate summary results for each IP/cfg file
        '''
        return

    def _get_results_page_link(self, link_text):
        if not self.args.publish: return link_text
        results_page_url = self.results_server_page.replace(
            self.results_server_prefix, self.results_server_url_prefix)
        return "[%s](%s)" % (link_text, results_page_url)

    def gen_email_html_summary(self):
        if self.is_master_cfg:
            gen_results = self.results_summary_md
        else:
            gen_results = self.results_md
        results_html = md_results_to_html(self.results_title, self.results_server_css_path,
                                          gen_results)
        results_html_file = self.scratch_root + "/email.html"
        f = open(results_html_file, 'w')
        f.write(results_html)
        f.close()
        log.info("[results summary]: %s [%s]", "generated for email purpose", results_html_file)

    def _publish_results(self):
        '''Publish results to the opentitan web server.
        Results are uploaded to {results_server_path}/latest/results.
        If the 'latest' directory exists, then it is renamed to its 'timestamp' directory.
        If the list of directories in this area is > 14, then the oldest entry is removed.
        Links to the last 7 regression results are appended at the end if the results page.
        '''
        if which('gsutil') is None or which('gcloud') is None:
            log.error(
                "Google cloud SDK not installed! Cannot access the results server"
            )
            return

        # Construct the paths
        results_page_url = self.results_server_page.replace(
            self.results_server_prefix, self.results_server_url_prefix)

        # Timeformat for moving the dir
        tf = "%Y.%m.%d_%H.%M.%S"

        # Extract the timestamp of the existing self.results_server_page
        cmd = self.results_server_cmd + " ls -L " + self.results_server_page + \
            " | grep \'Creation time:\'"

        log.log(VERBOSE, cmd)
        cmd_output = subprocess.run(cmd,
                                    shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.DEVNULL)
        log.log(VERBOSE, cmd_output.stdout.decode("utf-8"))
        old_results_ts = cmd_output.stdout.decode("utf-8")
        old_results_ts = old_results_ts.replace("Creation time:", "")
        old_results_ts = old_results_ts.strip()

        # Move the 'latest' to its timestamp directory if lookup succeeded
        if cmd_output.returncode == 0:
            try:
                if old_results_ts != "":
                    ts = datetime.datetime.strptime(
                        old_results_ts, "%a, %d %b %Y %H:%M:%S %Z")
                    old_results_ts = ts.strftime(tf)
            except ValueError as e:
                log.error(
                    "%s: \'%s\' Timestamp conversion value error raised!", e)
                old_results_ts = ""

            # If the timestamp conversion failed - then create a dummy one with
            # yesterday's date.
            if old_results_ts == "":
                log.log(VERBOSE,
                        "Creating dummy timestamp with yesterday's date")
                ts = datetime.datetime.now(
                    datetime.timezone.utc) - datetime.timedelta(days=1)
                old_results_ts = ts.strftime(tf)

            old_results_dir = self.results_server_path + "/" + old_results_ts
            cmd = self.results_server_cmd + " mv " + self.results_server_dir + \
                  " " + old_results_dir
            log.log(VERBOSE, cmd)
            cmd_output = subprocess.run(cmd,
                                        shell=True,
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.DEVNULL)
            log.log(VERBOSE, cmd_output.stdout.decode("utf-8"))
            if cmd_output.returncode != 0:
                log.error("Failed to mv old results page \"%s\" to \"%s\"!",
                          self.results_server_dir, old_results_dir)

        # Do an ls in the results root dir to check what directories exist.
        results_dirs = []
        cmd = self.results_server_cmd + " ls " + self.results_server_path
        log.log(VERBOSE, cmd)
        cmd_output = subprocess.run(args=cmd,
                                    shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.DEVNULL)
        log.log(VERBOSE, cmd_output.stdout.decode("utf-8"))
        if cmd_output.returncode == 0:
            # Some directories exist. Check if 'latest' is one of them
            results_dirs = cmd_output.stdout.decode("utf-8").strip()
            results_dirs = results_dirs.split("\n")
        else:
            log.log(VERBOSE, "Failed to run \"%s\"!", cmd)

        # Start pruning
        log.log(VERBOSE, "Pruning %s area to limit last 7 results",
                self.results_server_path)

        rdirs = []
        for rdir in results_dirs:
            dirname = rdir.replace(self.results_server_path, '')
            dirname = dirname.replace('/', '')
            if dirname == "latest": continue
            rdirs.append(dirname)
        rdirs.sort(reverse=True)

        rm_cmd = ""
        history_txt = "\n## Past Results\n"
        history_txt += "- [Latest](" + results_page_url + ")\n"
        if len(rdirs) > 0:
            for i in range(len(rdirs)):
                if i < 7:
                    rdir_url = self.results_server_path + '/' + rdirs[
                        i] + "/" + self.results_server_html
                    rdir_url = rdir_url.replace(self.results_server_prefix,
                                                self.results_server_url_prefix)
                    history_txt += "- [{}]({})\n".format(rdirs[i], rdir_url)
                elif i > 14:
                    rm_cmd += self.results_server_path + '/' + rdirs[i] + " "

        if rm_cmd != "":
            rm_cmd = self.results_server_cmd + " -m rm -r " + rm_cmd + "; "

        # Append the history to the results.
        results_md = self.results_md + history_txt

        # Publish the results page.
        # First, write the results html file temporarily to the scratch area.
        results_html_file = self.scratch_path + "/results_" + self.timestamp + ".html"
        f = open(results_html_file, 'w')
        f.write(
            md_results_to_html(self.results_title,
                               self.results_server_css_path, results_md))
        f.close()
        rm_cmd += "/bin/rm -rf " + results_html_file + "; "

        log.info("Publishing results to %s", results_page_url)
        cmd = self.results_server_cmd + " cp " + results_html_file + " " + \
              self.results_server_page + "; " + rm_cmd
        log.log(VERBOSE, cmd)
        try:
            cmd_output = subprocess.run(args=cmd,
                                        shell=True,
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT)
            log.log(VERBOSE, cmd_output.stdout.decode("utf-8"))
        except Exception as e:
            log.error("%s: Failed to publish results:\n\"%s\"", e, str(cmd))

    def publish_results(self):
        '''Public facing API for publishing results to the opentitan web server.
        '''
        for item in self.cfgs:
            item._publish_results()

        if self.is_master_cfg: self.publish_results_summary()

    def publish_results_summary(self):
        '''Public facing API for publishing md format results to the opentitan web server.
        '''
        results_html_file = "summary_" + self.timestamp + ".html"
        results_page_url = self.results_summary_server_page.replace(
            self.results_server_prefix, self.results_server_url_prefix)

        # Publish the results page.
        # First, write the results html file temporarily to the scratch area.
        f = open(results_html_file, 'w')
        f.write(
            md_results_to_html(self.results_title,
                               self.results_server_css_path,
                               self.results_summary_md))
        f.close()
        rm_cmd = "/bin/rm -rf " + results_html_file + "; "

        log.info("Publishing results summary to %s", results_page_url)
        cmd = self.results_server_cmd + " cp " + results_html_file + " " + \
              self.results_summary_server_page + "; " + rm_cmd
        log.log(VERBOSE, cmd)
        try:
            cmd_output = subprocess.run(args=cmd,
                                        shell=True,
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT)
            log.log(VERBOSE, cmd_output.stdout.decode("utf-8"))
        except Exception as e:
            log.error("%s: Failed to publish results:\n\"%s\"", e, str(cmd))

    def has_errors(self):
        return self.errors_seen
