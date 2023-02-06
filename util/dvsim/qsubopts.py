#!/usr/bin/env python
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# -*- coding: utf-8 -*-
# ----------------------------------
# qsubOptions Class
# ----------------------------------
"""A helper class designed to handle the managment of options and
positional arguments to qsub and related Grid Engine executables.

Contains functions to write the requested execution string either
to the command line or to a script file.
"""

import argparse


class qsubOptions():
    "A data type meant to collect qsub options. See man qsub for information"

    def __init__(self, optstring='', prog='qsub'):
        # Which SGE command are we going to work with?
        self.prog = prog
        sge_program_names = [
            'qsub', 'qrsh', 'qsh', 'qlogin', 'qalter', 'qresub', 'qmake'
        ]
        assert self.prog in sge_program_names, 'Unsupported SGE command: ' + prog + \
            'not one of ' + ', '.join(sge_program_names)

        if prog == 'qmake' and '-pe' in optstring:
            prog = 'qsub'
        else:
            prog = 'qrsh'

        # SUPPRESS = If not specified, do not generate variable in namespace
        self.parser = argparse.ArgumentParser(
            description='Options to pass to qsub',
            formatter_class=argparse.RawTextHelpFormatter,
            argument_default=argparse.SUPPRESS,
            epilog="""The following is scraped from the qsub manpage for GE \
            6.2u5 dated 2009/12/01 12:24:06""")

        # BEGIN SGE OPTION PARSER
        # BUG if help still begins with a line with -option, have cosmetic bug where
        # metavar cannot be specified correctly

        yesno = ['y', 'yes', 'n', 'no']

        if prog in ['qsub', 'qrsh', 'qsh', 'qlogin']:
            self.parser.add_argument('-@',
                                     metavar='optionfile',
                                     help="""\
              Forces qsub, qrsh, qsh, or qlogin to use the options contained
              in optionfile. The indicated file may contain all
              valid options. Comment lines must start with a "#" sign.""")

        if prog in ['qsub', 'qalter']:
            self.parser.add_argument('-a',
                                     metavar='date_time',
                                     help="""\
              Available for qsub and qalter only.

              Defines or redefines the time and date at  which  a  job  is  eligible
              for  execution.  Date_time  conforms  to [[CC]]YY]MMDDhhmm[.SS],
              for the details, please see Date_time in: sge_types(1).

              If  this  option is used with qsub or if a corresponding value is specified
              in qmon then a parameter named a and the value in the format CCYYMMDDhhmm.SS
              will be passed to the defined JSV instances (see -jsv  option  below  or
              find more information concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-ac',
                                     metavar='variable[=value]',
                                     action='append',
                                     help=""" -ac variable[=value],...
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Adds  the  given  name/value  pair(s)  to the job's context. Value may be omitted.
              Grid Engine appends the given argument to the list of context variables for the job.
              Multiple -ac, -dc, and -sc options may  be  given.   The order is important here.

              The  outcome  of  the  evaluation  of all -ac, -dc, and -sc options or
              corresponding values in qmon is passed to defined JSV instances as parameter
              with the name ac.  (see -jsv option below or find more information concerning
              JSV in jsv(1)) QALTER allows changing this option even while the job executes."""
                                     )

        if prog in ['qsub', 'qalter', 'qrsh', 'qsh', 'qlogin']:
            self.parser.add_argument('-ar',
                                     metavar='ar_id',
                                     help="""\
              Available for qsub, qalter, qrsh, qsh, or qlogin only.

              Assigns  the  submitted  job  to  be  a  part of an existing Advance Reservation.
              The complete list of existing
              Advance Reservations can be obtained using the qrstat(1) command.

              Note that the -ar option adds implicitly the -w e option if not otherwise requested.

              Qalter allows changing this option even while the job executes.
              The modified parameter will only  be  in  effect
              after a restart or migration of the job however.

              If  this  option  or  a  corresponding  value in qmon is specified
              then this value will be passed to defined JSV instances as parameter
              with the name ar.  (see -jsv option below or find  more  information
              concerning  JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-A',
                                     metavar='account_string',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Identifies the account to which the resource consumption of the
              job should be charged. The account_string should
              conform to the name definition in M sge_types 1 .
              In the absence of this parameter Grid Engine will  place  the
              default account string "ge" in the accounting record of the job.
              Qalter allows changing this option even while the job executes.

              If  this  option  or  a  corresponding  value in qmon is specified
              then this value will be passed to defined JSV instances as parameter with the name A.
              (see -jsv option below or  find  more  information  concerning  JSV  in jsv(1))"""
                                     )

        self.parser.add_argument('-binding',
                                 nargs='+',
                                 metavar=('binding_instance',
                                          'binding_strategy'),
                                 help="""\
       -binding [ binding_instance ] binding_strategy

              A  job  can  request a specific processor core binding (processor affinity)
              with this parameter. This request is neither a hard nor a soft request,
              it is a hint for the execution host to do this if possible.  Please note that
              the  requested binding strategy is not used for resource  selection  within
              Grid Engine.  As a result an execution host might be selected where Grid Engine
              does not even know the hardware topology and therefore is not able
              to apply the requested binding.

              To enforce Grid Engine to select hardware on which the binding can be applied
              please use the -l switch in combination with the complex attribute m_topology.

              binding_instance is an optional parameter.
              It might either be env, pe or set depending on which instance  should
              accomplish the job to core binding. If the value for binding_instance
              is not specified then set will be used.

              env  means  that  the  environment variable SGE_BINDING will be exported
              to the job environment of the job. This variable contains the selected
              operating system internal processor numbers.  They might be  more  than  selected
              cores  in  presence of SMT or CMT because each core could be represented
              by multiple processor identifiers.  The processor numbers are space separated.

              pe means that the information about the selected cores appears in
              the fourth column of the pe_hostfile. Here the logical  core  and
              socket numbers are printed (they start at 0 and have no holes)
              in colon separated pairs (i.e. 0,0:1,0 which means core 0 on socket 0 and
              core 0 on socket 1).  For more  information  about  the  $pe_hostfile
              check ge_pe(5)

              set (default if nothing else is specified). The binding strategy is applied
              by Grid Engine. How this is achieved depends on the underlying hardware
              architecture of the execution host where the submitted job will be started.

              On Solaris 10 hosts a processor set will be created where the job can
              exclusively run in.  Because of  operating system limitations at least
              one core must remain unbound. This resource could of course used by an unbound job.

              On  Linux  hosts  a  processor affinity mask will be set to restrict  the job
              to run exclusively on the selected cores.
              The operating system allows other unbound processes to use these cores.
              Please note that on  Linux  the binding  requires  a  Linux  kernel
              version of 2.6.16 or greater. It might be even possible to use a kernel with
              lower version number but in that case additional kernel patches have to be
              applied. The loadcheck  tool  in  the utilbin directory can be used to check
              if the hosts capabilities.  You can also use the -sep in combination with
              -cb of qconf(5) command to identify if Grid Engine is able to recognize the
              hardware topology.

              Possible values for binding_strategy are as follows:

                  linear:<amount>[:<socket>,<core>]
                  striding:<amount>:<n>[:<socket>,<core>]
                  explicit:[<socket>,<core>;...]<socket>,<core>

              For the binding strategy linear and striding there is an optional
              socket and core pair attached.
              These  denotes the mandatory starting point for the first core to bind on.

              linear  means  that  Grid Engine tries to bind the job on amount successive cores.
              If socket and core is omitted then Grid Engine first allocates successive cores
              on the first empty socket found.  Empty means that  there  are
              no  jobs bound to the socket by Grid Engine.  If this is not  possible or is
              not sufficient Grid Engine tries to
              find (further) cores on the socket with the most unbound cores and so on.
              If the amount of allocated  cores  is
              lower  than  requested  cores,  no binding is done for the job.
              If socket and core is specified then Grid Engine
              tries to find amount of empty cores beginning with this starting point.
              If this is not possible then binding  is not done.

              striding means that Grid Engine tries to find cores with a certain offset.
              It will select amount of empty cores with a offset of n -1 cores in between.
              Start point for the search algorithm is socket 0  core  0.  As  soon  as
              amount  cores are found they will be used to do the job binding.
              If there are not enough empty cores or if correct offset cannot be
              achieved then there will be no binding done.

              explicit binds the specified sockets and cores that  are  mentioned
              in  the  provided  socket/core  list.  Each socket/core  pair  has to
              be specified only once.If a socket/core pair is already in use by a different job the
              whole binding request will be ignored.

              Qalter allows changing this option even while the job executes.
              The modified parameter will only  be  in  effect
              after a restart or migration of the job, however.

              If  this  option  or  a corresponding value in qmon is specified then these values
              will be passe to defined JSV instances as parameters with the names binding_strategy,
              binding_type, binding_amount,  binding_step,  binding_socket,
              binding_core, binding_exp_n, binding_exp_socket<id>, binding_exp_core<id>.

              Please  note that the length of the socket/core value list of the explicit binding is
              reported as binding_exp_n.
              <id> will be replaced by the position of the socket/core pair  within  the  explicit
              list  (0  <=  id  <  binding_exp_n).   The first socket/core pair of the explicit
              binding will be reported with the parameter names bind-
              ing_exp_socket0 and binding_exp_core0.

              Values that do not apply for the specified binding will not be reported to JSV.
              E.g. binding_step will only  be
              reported for the striding binding and all binding_exp_* values will passed to
              JSV if explicit binding was speci‐
              fied.  (see -jsv  option  below or find more information concerning
              JSV in jsv(1))""")

        if prog in ['qsub', 'qrsh']:
            self.parser.add_argument('-b',
                                     choices=yesno,
                                     help="""\
              Available for qsub, qrsh only. Qalter does not allow changing this option.
              This option cannot be embedded in the script file itself.

              Gives  the user the possibility to indicate explicitly whether command should be
              treated as binary or script. If the value of -b is 'y', then command  may be a
              binary or script.  The command might not be accessible  from  the
              submission  host.   Nothing  except  the path of the command will be
              transferred from the submission host to the
              execution host. Path aliasing will be applied to the path of command
              before command will be executed.

              If the value of -b is 'n' then command needs to be a script and it will
              be handled as script.  The  script  file
              has to be accessible by the submission host.
              It will be transferred to the execution host. qsub/qrsh will search
              directive prefixes within script.

              qsub will implicitly use -b n whereas qrsh will apply the -b y option
              if nothing else is specified.

              The value specified with this option or the corresponding value
              specified in qmon will only be passed to defined
              JSV instances if the value is yes.  The name of the parameter will be b.
              The value will be y also when then long
              form yes was specified during submission.
              (see -jsv option below or find more  information  concerning  JSV  in
              jsv(1))

              Please  note  that  submission of command as script (-b n) can have a
              significant performance impact,especially for short running jobs and big job scripts.
              Script submission adds a number of  operations  to  the  submission
              process: The job script needs to be
              - parsed at client side (for special comments)
              - transferred from submit client to qmaster
              - spooled in qmaster
              - transferred to execd at job execution
              - spooled in execd
              - removed from spooling both in execd and qmaster once the job is done
              If job scripts are available on the execution nodes, e.g. via NFS, binary
              submission can be the better choice.""")

        if prog in ['qsub', 'qalter']:
            self.parser.add_argument('-c',
                                     metavar='occasion_specifier',
                                     help="""\
              Available for qsub and qalter only.

              Defines or redefines whether the job should be checkpointed, and if so,
              under what circumstances. The specifica‐
              tion of the checkpointing occasions with this option overwrites the
              definitions of the  when  parameter  in  the
              checkpointing  environment  (see  checkpoint(5)) referenced by the qsub
              -ckpt switch.  Possible values for occa‐
              sion_specifier are

              n           no checkpoint is performed.
              s           checkpoint when batch server is shut down.
              m           checkpoint at minimum CPU interval.
              x           checkpoint when job gets suspended.
              <interval>  checkpoint in the specified time interval.

              The minimum CPU interval is defined in the queue configuration (see
              queue_conf(5) for details).  <interval>  has
              to  be specified in the format hh:mm:ss.
              The maximum of <interval> and the queue's minimum CPU interval is used
              if <interval> is specified. This is done to ensure that a machine is not
              overloaded by checkpoints being  generated too frequently.

              The  value specified with this option or the corresponding value specified
              in qmon will be passed to defined JSV
              instances.  The <interval> will be available as parameter with the  name  c_interval.
              The  character  sequence
              specified will be available as parameter with the name c_occasion.
              Please note that if you change c_occasion via
              JSV then the last setting of c_interval will be overwritten and vice versa.
              (see -jsv option below or find more
              information concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qalter']:
            self.parser.add_argument('-ckpt',
                                     metavar='ckpt_name',
                                     help="""\
              Available for qsub and qalter only.

              Selects  the  checkpointing  environment (see checkpoint(5)) to be used
              for checkpointing the job. Also declares the job to be a checkpointing job.

              If this option or a corresponding value in qmon is specified then this
              value  will  be  passed  to  defined  JSV
              instances  as  parameter  with the name ckpt.  (see -jsv option below or
              find more information concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin']:
            self.parser.add_argument('-clear',
                                     action='store_true',
                                     help="""\
              Available for qsub, qsh, qrsh, and qlogin only.

              Causes all elements of the job to be reset to the initial default
              status prior to applying any modifications (if
              any) appearing in this specific command.""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qalter']:
            self.parser.add_argument('-cwd',
                                     action='store_true',
                                     help="""\
              Available for qsub, qsh, qrsh and qalter only.

              Execute  the  job  from  the  current  working directory.
              This switch will activate Grid Engine's path aliasing
              facility, if the corresponding configuration files are present (see ge_aliases(5)).

              In the case of qalter, the previous definition of the current working
              directory will be overwritten if qalter is
              executed from a different directory than the preceding qsub or qalter.

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.

              If this option or a corresponding value in qmon is specified
              then this value  will  be  passed  to  defined  JSV
              instances  as  parameter with the name cwd. The value of this parameter
              will be the absolute path to the current
              working directory. JSV scripts can remove the path from jobs during the
              verification  process  by  setting  the
              value  of this parameter to an empty string.
              As a result the job behaves as if -cwd was not specified during job
              submission.  (see -jsv option below or find more information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qrsh']:
            self.parser.add_argument('-C',
                                     metavar='prefix_string',
                                     help="""\
              Available for qsub and qrsh with script submission (-b n).

              Prefix_string defines the prefix that declares a directive in the  job's  command.
              The  prefix  is  not  a  job
              attribute,  but  affects  the  behavior  of  qsub  and qrsh.
              If prefix is a null string, the command will not be
              scanned for embedded directives.
              The directive prefix consists of two ASCII characters which,
              when appearing in the first two bytes of  a  script
              line, indicate that what follows is an Grid Engine command.  The default is "#$".
              The  user  should  be aware that changing the first delimiting character
              can produce unforeseen side effects. If
              the script file contains anything other than a "#" character in the first byte
              position of the line,  the  shell
              processor for the job will reject the line and may exit the job prematurely.
              If the -C option is present in the script file, it is ignored."""
                                     )

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-dc',
                                     action='append',
                                     metavar='variable',
                                     help="""\
       -dc variable,...
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Removes  the  given  variable(s)  from the job's context.  Multiple -ac, -dc, and
              -sc options may be given.  The order is important.

              Qalter allows changing this option even while the job executes.

              The outcome of the evaluation of all -ac, -dc, and -sc options or corresponding
              values  in  qmon  is  passed  to
              defined JSV instances as parameter with the name ac.  (see -jsv option below or
              find more information concerning
              JSV in jsv(1))""")

        if prog in ['qsh', 'qrsh']:
            self.parser.add_argument('-display',
                                     metavar='display_specifier',
                                     help="""\
              Available for qsh and qrsh.

              Directs xterm(1) to use display_specifier in order to contact the X server.
              The display_specifier has  to  con‐
              tain  the  hostname  part  of the display name (e.g. myhost:1).
              Local display names (e.g. :0) cannot be used in
              grid environments.  Values set with the -display option overwrite settings
              from the submission  environment  and
              from -v command line options.

              If  this  option  or  a  corresponding  value in qmon is specified then this
              value will be passed to defined JSV
              instances as parameter with the name display. This value will also be available
              in  the  job  environment  which
              might  optionally  be  passed to JSV scripts. The variable name will be DISPLAY.
              (see -jsv option below or find
              more information concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-dl',
                                     metavar='date_time',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Specifies the deadline initiation time in [[CC]YY]MMDDhhmm[.SS] format (see -a
              option above). The deadline  ini‐
              tiation time is the time at which a deadline job has to reach top priority to be
              able to complete within a given
              deadline. Before the deadline initiation time the priority of a deadline job
              will be raised  steadily  until  it
              reaches the maximum as configured by the Grid Engine administrator.

              This option is applicable only for users allowed to submit deadline jobs.

              If  this  option  or  a  corresponding  value in qmon is specified then this
              value will be passed to defined JSV
              instances as parameter with the name dl. The format for the date_time value
              is CCYYMMDDhhmm.SS (see -jsv  option
              below or find more information concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-e',
                                     metavar='path',
                                     help="""\
          -e [[hostname]:]path,...
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Defines  or  redefines the path used for the standard error stream of the job.
              For qsh, qrsh and qlogin only the
              standard error stream of prolog and epilog is redirected.  If the path
              constitutes an absolute  path  name,  the
              error-path  attribute  of  the  job  is  set to path, including the hostname.
              If the path name is relative, Grid
              Engine expands path either with the current working directory path
              (if the -cwd switch (see above) is also spec‐
              ified)  or with the home directory path. If hostname is present,
              the standard error stream will be placed in the
              corresponding location only if the job runs on the specified host.
              If the path contains a ":"  without  a  host‐
              name, a leading ":" has to be specified.

              By  default  the  file name for interactive jobs is /dev/null.
              For batch jobs the default file name has the form
              job_name.ejob_id and job_name.ejob_id.task_id for array job tasks (see -t option
              below).

              If path is a directory, the standard error stream of the job will be put
              in this  directory  under  the  default
              file  name.  If the pathname contains certain pseudo environment variables,
              their value will be expanded at run‐
              time of the job and will be used to constitute the standard error stream path name.
              The following  pseudo  envi‐
              ronment variables are supported currently:

              $HOME       home directory on execution machine
              $USER       user ID of job owner
              $JOB_ID     current job ID
              $JOB_NAME   current job name (see -N option)
              $HOSTNAME   name of the execution host
              $TASK_ID    array job task index number

              Alternatively  to  $HOME  the tilde sign "~" can be used as common in csh(1)
              or ksh(1).  Note, that the "~" sign
              also works in combination with user names, so that "~<user>" expands to the
              home  directory  of  <user>.  Using
              another user ID than that of the job owner requires corresponding permissions,
              of course.

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.

              If this option or a corresponding value in qmon is specified then this value
              will  be  passed  to  defined  JSV
              instances  as  parameter  with  the  name  e.  (see -jsv option below or
              find more information concerning JSV in
              jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-hard',
                                     action='store_true',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Signifies that all -q and -l resource requirements following in the command
              line will be hard  requirements  and
              must be satisfied in full before a job can be scheduled.
              As Grid Engine scans the command line and script file for Grid Engine options
              and parameters it builds a list of
              resources required by a job. All such resource requests are considered as
              absolutely essential for  the  job  to
              commence. If the -soft option (see below) is encountered during the scan then
              all following resources are desig‐
              nated as "soft requirements" for execution, or "nice-to-have, but not essential".
              If the -hard flag  is  encoun‐
              tered  at a later stage of the scan, all resource requests following it once again
              become "essential". The -hard
              and -soft options in effect act as "toggles" during the scan.

              If this option or a corresponding value in qmon is specified then the corresponding
              -q and -l resource  require‐
              ments  will  be passed to defined JSV instances as parameter with the names
              q_hard and l_hard. Find for informa‐
              tion in the sections describing -q and -l.  (see -jsv option below or find
              more information  concerning  JSV  in
              jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qalter', 'qresub']:
            # NOTE in SGE this is -h, here I have renamed it to -hold
            # TODO check if multiple holds are parsed correctly
            self.parser.add_argument('-hold',
                                     choices='usonUOS',
                                     help="""\
              NOTE: Originally defined as -h, but changed to -hold here.

              Available for qsub (only -h), qrsh, qalter and qresub (hold state is
              removed when not set explicitly).

              List of holds to place on a job, a task or some tasks of a job.

              `u'  denotes a user hold.
              `s'  denotes a system hold.
              `o'  denotes a operator hold.
              `n'  denotes no hold (requires manager privileges).

              As  long  as  any hold other than `n' is assigned to the job the job is
              not eligible for execution. Holds can be
              released via qalter and qrls(1).  In case of qalter this is supported
              by the following additional option  speci‐
              fiers for the -h switch:

              `U'  removes a user hold.
              `S'  removes a system hold.
              `O'  removes a operator hold.

              Grid  Engine managers can assign and remove all hold types,
              Grid Engine operators can assign and remove user and
              operator holds, and users can only assign or remove user holds.

              In the case of qsub only user holds can be placed on a job and thus
              only the first form of the option  with  the
              -h switch alone is allowed.  As opposed to this, qalter requires
              the second form described above.

              An alternate means to assign hold is provided by the qhold(1) facility.

              If the job is a array job (see the -t option below), all tasks specified via
              -t are affected by the -h operation
              simultaneously.

              Qalter allows changing this option even while the job executes.
              The modified parameter will only  be  in  effect
              after a restart or migration of the job, however.

              If  this  option  is specified with qsub or during the submission
              of a job in qmon then the parameter h with the
              value u will be passed to the defined JSV instances indicating that
              the job will be in user hold after the  sub‐
              mission finishes.  (see -jsv option below or find more information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qalter']:
            self.parser.add_argument('-hold_jid',
                                     nargs='+',
                                     metavar='wc_job_list',
                                     help="""\
              Available for qsub, qrsh, and qalter only. See sge_types(1).
              for wc_job_list definition.

              Defines  or  redefines  the job dependency list of the submitted job.
              A reference by job name or pattern is only
              accepted if the referenced job is owned by the same user as the referring job.
              The submitted job is not eligible
              for  execution unless all jobs referenced in the comma-separated job id and/or
              job name list have completed.  If
              any of the referenced jobs exits with exit code 100, the submitted
              job will remain ineligible for execution.

              With the help of job names or regular pattern one can specify a job
              dependency on multiple jobs  satisfying  the
              regular  pattern  or  on all jobs with the requested name.
              The name dependencies are resolved at submit time and
              can only be changed via qalter. New jobs or name changes
              of other jobs will not be taken into account.

              Qalter allows changing this option even while the job executes.
              The modified parameter will only  be  in  effect
              after a restart or migration of the job, however.

              If  this  option  or  a  corresponding  value in qmon is specified
              then this value will be passed to defined JSV
              instances as parameter with the name hold_jid.
              (see -jsv option below or find more information  concerning  JSV
              in jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qalter']:
            self.parser.add_argument('-hold_jid_ad',
                                     nargs='+',
                                     metavar='wc_job_list',
                                     help="""\
              Available for qsub, qrsh, and qalter only. See sge_types(1).
              for wc_job_list definition.

              Defines  or  redefines the job array dependency list of
              the submitted job. A reference by job name or pattern is
              only accepted if the referenced job is owned by the same
              user as the referring job. Each sub-task of the submit‐
              ted  job  is  not eligible for execution unless the corresponding
              sub-tasks of all jobs referenced in the comma-
              separated job id and/or job name list have completed.
              If any array task of the referenced jobs exits with  exit
              code 100, the dependent tasks of the submitted job will remain
              ineligible for execution.

              With  the  help of job names or regular pattern one can specify
              a job dependency on multiple jobs satisfying the
              regular pattern or on all jobs with the requested name.
              The name dependencies are resolved at  submit  time  and
              can only be changed via qalter. New jobs or name changes of other
              jobs will not be taken into account.

              If  either  the submitted job or any job in wc_job_list are
              not array jobs with the same range of sub-tasks (see
              -t option below), the request list will be rejected and the
              job create or modify operation will error.

              qalter allows changing this option even while the job executes.
              The modified parameter will only  be  in  effect
              after a restart or migration of the job, however.

              If  this  option  or  a  corresponding  value in qmon is
              specified then this value will be passed to defined JSV
              instances as parameter with the name hold_jid_ad.
              (see -jsv option below or find  more  information  concerning
              JSV in jsv(1))""")

        if prog in ['qsub', 'qalter']:
            self.parser.add_argument('-i',
                                     metavar='file',
                                     help="""\
       -i [[hostname]:]file,...
              Available for qsub, and qalter only.

              Defines or redefines the file used for the standard input stream of
              the job. If the file constitutes an absolute
              filename, the input-path attribute of the job is set to path,
              including the hostname. If the path name is  rela‐
              tive, Grid Engine expands path either with the current working
              directory path (if the -cwd switch (see above) is
              also specified) or with the home directory path. If hostname is present,
              the  standard  input  stream  will  be
              placed  in  the  corresponding  location  only if the job runs
              on the specified host. If the path contains a ":"
              without a hostname, a leading ":" has to be specified.

              By default /dev/null is the input stream for the job.

              It is possible to use certain pseudo variables, whose values
              will be expanded at runtime of the job and will  be
              used to express the standard input stream as described in
              the -e option for the standard error stream.

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.

              If this option or a corresponding value in qmon is specified then
              this value  will  be  passed  to  defined  JSV
              instances  as  parameter  with  the  name  i.
              (see -jsv option below or find more information concerning JSV in
              jsv(1))""")

        if prog in ['qrsh', 'qmake']:
            self.parser.add_argument('-inherit',
                                     action='store_true',
                                     help="""\
              Available only for qrsh and qmake(1).

              qrsh allows the user to start a task in an already scheduled parallel job.
              The option -inherit  tells  qrsh  to
              read a job id from the environment variable JOB_ID and start the
              specified command as a task in this job. Please
              note that in this case, the hostname of the host where the command
              will be executed must precede the command  to
              execute; the syntax changes to

              qrsh -inherit [ other options ] hostname command [ command_args ]

              Note also, that in combination with -inherit, most other command line
              options will be ignored.  Only the options
              -verbose, -v and -V will be interpreted.  As a replacement to option
              -cwd please use -v PWD.

              Usually a task should have the same environment (including the
              current working directory) as  the  corresponding
              job, so specifying the option -V should be suitable for most applications.

              Note:  If  in  your  system  the qmaster tcp port is not configured as a service,
              but rather via the environment
              variable GE_QMASTER_PORT, make sure that this variable is set in the
              environment when calling qrsh or qmake with
              the  -inherit  option.  If  you  call  qrsh  or  qmake with the
              -inherit option from within a job script, export
              GE_QMASTER_PORT with the option "-v GE_QMASTER_PORT" either as
              a command argument or an embedded directive.

              This parameter is not available in the JSV context.
              (see -jsv option below or find more information  concerning
              JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-j',
                                     choices=yesno,
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Specifies whether or not the standard error stream of the job
              is merged into the standard output stream.
              If both the -j y and the -e options are present,
              Grid Engine sets but ignores the error-path attribute.

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.


              The value specified with this option or the corresponding
              value specified in qmon will only be passed to defined
              JSV instances if the value is yes.  The name of the parameter will be j.
              The value will be y also when then long
              form yes was specified during submission.
              (see -jsv option below or find more  information  concerning  JSV  in
              jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-js',
                                     nargs='?',
                                     type=int,
                                     metavar='job_share',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Defines  or  redefines the job share of the job relative to other jobs.
              Job share is an unsigned integer value.
              The default job share value for jobs is 0.

              The job share influences the Share Tree Policy and the Functional Policy.
              It has no effect on  the  Urgency  and
              Override  Policies  (see  share_tree(5), sched_conf(5) and the
              Grid Engine Installation and Administration Guide
              for further information on the resource management policies supported
              by Grid Engine).

              In case of the Share Tree Policy, users can distribute the tickets to
              which they are  currently  entitled  among
              their  jobs  using different shares assigned via -js.
              If all jobs have the same job share value, the tickets are
              distributed evenly. Otherwise, jobs receive tickets relative
              to the different job shares. Job shares are treated
              like an additional level in the share tree in the latter case.

              In  connection  with  the  Functional Policy, the job share can be
              used to weight jobs within the functional job
              category.  Tickets are distributed relative to any uneven
              job share distribution treated as a virtual share dis‐
              tribution level underneath the functional job category.

              If  both  the  Share Tree and the Functional Policy are active,
              the job shares will have an effect in both poli‐
              cies, and the tickets independently derived in each of them are
              added to the total number of  tickets  for  each
              job.

              If  this  option  or  a  corresponding  value in qmon is specified
              then this value will be passed to defined JSV
              instances as parameter with the name js.  (see -jsv option below or
              find  more  information  concerning  JSV  in
              jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin']:
            self.parser.add_argument('-jsv',
                                     metavar='jsv_url',
                                     help="""\
              Available for qsub, qsh, qrsh and qlogin only.

              Defines  a  client JSV instance which will be executed to
              verify the job specification before the job is sent to
              qmaster.

              In contrast to other options this switch will not be overwritten
              if  it  is  also  used  in  sge_request  files.
              Instead all specified JSV instances will be executed to verify
              the job to be submitted.

              The  JSV  instance  which is directly passed with the commandline
              of a client is executed as first to verify the
              job specification. After that the JSV instance which might have
              been defined in various sge_request  files  will
              be triggered to check the job. Find more details
              in man page jsv(1) and sge_request(5).

              The syntax of the jsv_url is specified in sge_types(1).()""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-l',
                                     metavar='keywords',
                                     help="""\
       -l resource=value,...
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Launch  the  job in a Grid Engine queue meeting the given resource
              request list.  In case of qalter the previous
              definition is replaced by the specified one.

              complex(5) describes how a list of available resources and  their
              associated  valid  value  specifiers  can  be
              obtained.

              There  may  be  multiple -l switches in a single command.
              You may request multiple -l options to be soft or hard
              both in the same command line. In case of a serial job multiple
              -l switches refine the definition for the sought
              queue.

              Qalter  allows  changing the value of this option even while the
              job is running, but only if the initial list of
              resources does not contain a resource that is marked as consumable.
              However the modification will only be effec‐
              tive after a restart or migration of the job.

              If  this option or a corresponding value in qmon is specified the
              these hard and soft resource requirements will
              be passed to defined JSV instances as parameter with the names
              l_hard and l_soft. If regular expressions will be
              used  for  resource requests, then these expressions will
              be passed as they are. Also shortcut names will not be
              expanded.  (see -jsv option above or find more information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            # TODO check if multiple arguments are parsed correctly
            self.parser.add_argument('-m',
                                     nargs='+',
                                     choices='beasn',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Defines or redefines under which circumstances mail
              is to be sent to the job owner or to the users defined  with
              the -M option described below. The option arguments
              have the following meaning:

              `b'     Mail is sent at the beginning of the job.
              `e'     Mail is sent at the end of the job.
              `a'     Mail is sent when the job is aborted or
                      rescheduled.
              `s'     Mail is sent when the job is suspended.
              `n'     No mail is sent.

              Currently no mail is sent when a job is suspended.

              Qalter  allows  changing the b, e, and a option arguments
              even while the job executes. The modification of the b
              option argument will only be in effect after a restart
              or migration of the job, however.

              If this option or a corresponding value in qmon is
              specified then this value  will  be  passed  to  defined  JSV
              instances as parameter with the name m.  (see -jsv option
              above or find more information concerning JSV in""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-M',
                                     metavar='user[@host]',
                                     help="""\
       -M user[@host],...
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Defines or redefines the list of users to which the server
              that executes the job has to send mail, if the server
              sends mail about the job.  Default is the job owner at the originating host.

              Qalter allows changing this option even while the job executes.

              If this option or a corresponding value in qmon is specified then
              this value  will  be  passed  to  defined  JSV
              instances  as  parameter  with  the  name  M.  (see -jsv option above or
              find more information concerning JSV in
              jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-masterq',
                                     nargs='+',
                                     metavar='wc_queue_list',
                                     help="""\
              Available for qsub, qrsh, qsh, qlogin and qalter.  Only meaningful
              for parallel jobs, i.e. together with the -pe option.

              Defines or redefines a list of cluster queues, queue domains and
              queue instances which may be used to become the
              so called master queue of this parallel job. A more detailed
              description  of  wc_queue_list  can  be  found  in
              sge_types(1).   The  master queue is defined as the queue where
              the parallel job is started. The other queues to
              which the parallel job spawns tasks are called slave queues.
              A parallel job only has one master queue.

              This parameter has all the properties of a resource request
              and will be merged with  requirements  derived  from
              the -l option described above.

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.

              If this option or a corresponding value in qmon is specified
              the this hard resource requirement will  be  passed
              to  defined  JSV  instances as parameter with the name masterq.
              (see -jsv option above or find more information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qalter']:
            self.parser.add_argument('-notify',
                                     action='store_true',
                                     help="""\
              Available for qsub, qrsh (with command) and qalter only.

              This flag, when set causes Grid Engine to send "warning" signals
              to a running job prior to sending  the  signals
              themselves.  If  a  SIGSTOP  is pending, the job will receive
              a SIGUSR1 several seconds before the SIGSTOP. If a
              SIGKILL is pending, the job will receive a SIGUSR2 several
              seconds before the SIGKILL.  This option provides the
              running  job, before receiving the SIGSTOP or SIGKILL,
              a configured time interval to do e.g. cleanup operations.
              The amount of time delay is controlled by the notify parameter
              in each queue configuration (see queue_conf(5)).

              Note that the Linux operating system "misused" the user
              signals SIGUSR1 and SIGUSR2 in some early  Posix  thread
              implementations.  You might not want to use the
              -notify option if you are running multi-threaded applications in
              your jobs under Linux, particularly on 2.0 or earlier kernels.

              Qalter allows changing this option even while the job executes.

              Only if this option is used the parameter named notify with
              the value y will be passed to defined JSV instances.
              (see -jsv option above or find more information concerning
              JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin']:
            self.parser.add_argument('-now',
                                     choices=yesno,
                                     help="""\
              Available for qsub, qsh, qlogin and qrsh.

              -now y tries to start the job immediately or not at all.
              The command returns 0 on success, or 1 on failure (also
              if the job could not be scheduled immediately).
              For array jobs submitted with the -now  option,  if  all  tasks
              cannot be immediately scheduled, no tasks are scheduled.
              -now y is default for qsh, qlogin and qrsh

              With  the -now n option, the job will be put into the pending
              queue if it cannot be executed immediately. -now n
              is default for qsub.

              The value specified with this option or the corresponding
              value specified in qmon will only be passed to defined
              JSV  instances  if  the value is yes.  The name of the
              parameter will be now. The value will be y also when then
              long form yes was specified during submission.
              (see -jsv option above or find more information  concerning  JSV
              in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-N',
                                     metavar='name',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              The  name  of  the job. The name should follow the "name"
              definition in sge_types(1).  Invalid job names will be
              denied at submit time.

              If the -N option is not present, Grid Engine assigns
              the name of the job script to the job after  any  directory
              pathname has been removed from the script-name.
              If the script is read from standard input, the job name defaults
              to STDIN.

              In the case of qsh or qlogin with the -N option is absent,

              the string `INTERACT' is assigned to the job.

              In the case of qrsh if the -N option is absent, the resulting
              job name is determined from the qrsh command  line
              by  using the argument string up to the first
              occurrence of a semicolon or whitespace and removing the directory
              pathname.

              Qalter allows changing this option even while the job executes.

              The value specified with this option or the corresponding value
              specified in qmon will be passed to defined  JSV
              instances  as  parameter  with  the  name  N.  (see -jsv
              option above or find more information concerning JSV in
              jsv(1))""")

        if prog in ['qrsh']:
            self.parser.add_argument('-noshell',
                                     action='store_true',
                                     help="""\
              Available only for qrsh with a command line.

              Do not start the command line given to qrsh in a user's login shell,
              i.e.   execute  it  without  the  wrapping
              shell.

              This  option  can  be used to speed up execution as some overhead,
              like the shell startup and sourcing the shell
              resource files, is avoided.

              This option can only be used if no shell-specific command line
              parsing is required. If the command line contains
              shell  syntax  like environment variable substitution or (back) quoting,
              a shell must be started.  In this case,
              either do not use the -noshell option or include the shell call in the command line.

              Example:
              qrsh echo '$HOSTNAME'
              Alternative call with the -noshell option
              qrsh -noshell /bin/tcsh -f -c 'echo $HOSTNAME'""")

        if prog in ['qrsh']:
            self.parser.add_argument('-nostdin',
                                     action='store_true',
                                     help="""\
              Available only for qrsh.

              Suppress the input stream STDIN - qrsh will pass the option -n
              to the rsh(1) command. This is especially useful,
              if  multiple tasks are executed in parallel using qrsh, e.g.
              in a make(1) process - it would be undefined, which
              process would get the input.""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-o',
                                     metavar='path',
                                     help="""\
       -o [[hostname]:]path,...
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              The path used for the standard output stream of the job.
              The path is handled as described in the -e  option  for
              the standard error stream.

              By  default  the  file  name  for standard output has the
              form job_name.ojob_id and job_name.ojob_id.task_id for
              array job tasks (see -t option below).

              Qalter allows changing this option even while the job executes.
              The modified parameter will only  be  in  effect
              after a restart or migration of the job, however.

              If  this  option  or  a  corresponding  value in qmon is
              specified then this value will be passed to defined JSV
              instances as parameter with the name o.  (see -jsv option
              above or  find  more  information  concerning  JSV  in
              jsv(1))""")

        if prog in ['qalter']:
            self.parser.add_argument('-ot',
                                     metavar='override_tickets',
                                     help="""\
              Available for qalter only.

              Changes the number of override tickets for the specified job.
              Requires manager/operator privileges.""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-P',
                                     metavar='project_name',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Specifies  the  project  to which this job is assigned.
              The administrator needs to give permission to individual
              users to submit jobs to a specific project. (see -aprj option to qconf(1)).

              If this option or a corresponding value in qmon is specified then
              this value  will  be  passed  to  defined  JSV
              instances  as  parameter  with  the  name ot.  (see -jsv option
              above or find more information concerning JSV in
              jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-p',
                                     metavar='priority',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Defines or redefines the priority of the job relative to other jobs.
              Priority is an integer in the range  -1023
              to 1024.  The default priority value for jobs is 0.

              Users  may  only decrease the priority of their jobs.
              Grid Engine managers and administrators may also increase
              the priority associated with jobs. If a pending job has higher priority,
              it is earlier eligible for  being  dis‐
              patched by the Grid Engine scheduler.

              If  this  option or a corresponding value in qmon is specified and
              the priority is not 0 then this value will be
              passed to defined JSV instances as parameter with the name p.
              (see -jsv option above or find  more  information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-slot',
                                     metavar='slot',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Defines or redefines the priority of the job relative to other jobs.
              Priority is an integer in the range  -1023
              to 1024.  The default priority value for jobs is 0.

              Users  may  only decrease the priority of their jobs.
              Grid Engine managers and administrators may also increase
              the priority associated with jobs. If a pending job has higher priority,
              it is earlier eligible for  being  dis‐
              patched by the Grid Engine scheduler.

              If  this  option or a corresponding value in qmon is specified and
              the priority is not 0 then this value will be
              passed to defined JSV instances as parameter with the name p.
              (see -jsv option above or find  more  information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qsh', 'qrsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-pe',
                                     nargs=2,
                                     metavar=('parallel_environment', 'n'),
                                     help="""\
       -pe parallel_environment n[-[m]]|[-]m,...
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Parallel programming environment (PE) to instantiate.
              For more detail about PEs, please see the sge_types(1).

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.

              If this option or a corresponding value in qmon is specified
              then the parameters pe_name, pe_min and pe_max will
              be  passed to configured JSV instances where pe_name will be the
              name of the parallel environment and the values
              pe_min and pe_max represent the values n and m which have been
              provided with the -pe option. A missing  specifi‐
              cation  of  m  will be expanded as value 9999999 in JSV scripts
              and it represents the value infinity.  (see -jsv
              option above or find more information concerning JSV in jsv(1))"""
                                     )

        if prog in ['qrsh', 'qlogin']:
            self.parser.add_argument('-pty',
                                     choices=yesno,
                                     help="""\
              Available for qrsh and qlogin only.

              -pty yes enforces the job to be started in a pseudo terminal (pty).
              If no pty is available, the job start fails.
              -pty  no  enforces the job to be started without a pty.
              By default, qrsh without a command and qlogin start the
              job in a pty, qrsh with a command starts the job without a pty.

              This parameter is not available in the JSV context.
              (see -jsv option above or find more information  concerning
              JSV in jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-q',
                                     nargs='+',
                                     metavar='wc_queue_list',
                                     help="""\
              Available for qsub, qrsh, qsh, qlogin and qalter.

              Defines  or  redefines  a  list of cluster queues,
              queue domains or queue instances which may be used to execute
              this job. Please find a description of wc_queue_list in sge_types(1).
              This parameter has all the properties  of
              a resource request and will be merged with requirements derived from the
              -l option described above.

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.

              If this option or a corresponding value in qmon is specified
              the these hard and soft resource requirements  will
              be  passed  to defined JSV instances as parameters with the
              names q_hard and q_soft. If regular expressions will
              be used for resource requests, then these expressions will
              be passed as they are. Also shortcut names  will  not
              be expanded.  (see -jsv option above or find more information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-R',
                                     choices=yesno,
                                     help="""\
              Available for qsub, qrsh, qsh, qlogin and qalter.

              Indicates  whether a reservation for this job should be done.
              Reservation is never done for immediate jobs, i.e.
              jobs submitted using the -now yes option.  Please note that
              regardless of the reservation request, job  reserva‐
              tion  might  be disabled using max_reservation in sched_conf(5)
              and might be limited only to a certain number of
              high priority jobs.

              By default jobs are submitted with the -R n option.

              The value specified with this option or the corresponding value
              specified in qmon will only be passed to defined
              JSV instances if the value is yes.  The name of the parameter will be R.
              The value will be y also when then long
              form yes was specified during submission.
              (see -jsv option above or find more  information  concerning  JSV  in
              jsv(1))""")

        if prog in ['qsub', 'qalter']:
            self.parser.add_argument('-r',
                                     choices=yesno,
                                     help="""\
              Available for qsub and qalter only.

              Identifies  the  ability of a job to be rerun or not.
              If the value of -r is 'yes', the job will be rerun if the
              job was aborted without leaving a consistent exit state.
              (This is typically the case if the node on  which  the
              job is running crashes).  If -r is 'no',
              the job will not be rerun under any circumstances.
              Interactive jobs submitted with qsh, qrsh or qlogin are not rerunnable.

              Qalter allows changing this option even while the job executes.

              The value specified with this option or the corresponding value specified
              in qmon will only be passed to defined
              JSV instances if the value is yes.  The name of the parameter will be r.
              The value will be y also when then long
              form  yes  was  specified  during submission.  (see -jsv option above or
              find more information concerning JSV in
              jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-sc',
                                     action='append',
                                     metavar='variable[=value]',
                                     help="""\
       -sc variable[=value],...
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Sets the given name/value pairs as the job's context. Value may be omitted.
              Grid Engine replaces the job's  pre‐
              viously  defined  context  with the one given as the argument.
              Multiple -ac, -dc, and -sc options may be given.
              The order is important.

              Contexts provide a way to dynamically attach and remove meta-information
              to and from a job.  The  context  vari‐
              ables are not passed to the job's execution context in its environment.

              Qalter allows changing this option even while the job executes.

              The  outcome  of  the  evaluation  of all -ac, -dc, and -sc options
              or corresponding values in qmon is passed to
              defined JSV instances as parameter with the name ac.
              (see -jsv option above or find more information concerning
              JSV in jsv(1))""")

        if prog in ['qsub']:
            self.parser.add_argument('-shell',
                                     choices=yesno,
                                     help="""\
              Available only for qsub.

              -shell  n causes qsub to execute the command line directly,
              as if by exec(2).  No command shell will be executed
              for the job.  This option only applies when -b y is also used.
              Without -b y, -shell n has no effect.

              This option can be used to speed up execution as some overhead,
              like the shell startup and  sourcing  the  shell
              resource files is avoided.

              This option can only be used if no shell-specific command line parsing
              is required. If the command line contains
              shell syntax, like environment variable substitution or (back) quoting,
              a shell must be started.  In  this  case
              either  do  not  use  the -shell n option or execute the shell as the
              command line and pass the path to the exe‐
              cutable as a parameter.

              If a job executed with the -shell n option fails due to a user error,
              such as an invalid path to the executable,
              the job will enter the error state.

              -shell y cancels the effect of a previous -shell n.  Otherwise, it has no effect.

              See -b and -noshell for more information.

              The value specified with this option or the corresponding value
              specified in qmon will only be passed to defined
              JSV instances if the value is yes.  The name of the parameter
              will be shell. The value will be y also when  then
              long  form  yes was specified during submission.
              (see -jsv option above or find more information concerning JSV
              in jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-soft',
                                     action='store_true',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter only.

              Signifies that all resource requirements following in the command
              line will be soft requirements and are  to  be
              filled on an "as available" basis.
              As  Grid  Engine scans the command line and script file for
              Grid Engine options and parameters, it builds a list
              of resources required by the job. All such resource requests are
              considered as absolutely essential for the  job
              to  commence.  If the -soft option is encountered during the
              scan then all following resources are designated as
              "soft requirements" for execution, or "nice-to-have, but not essential".
              If  the  -hard  flag  (see  above)  is
              encountered  at a later stage of the scan, all resource requests following
              it once again become "essential". The
              -hard and -soft options in effect act as "toggles" during the scan.

              If this option or a corresponding value in qmon is
              specified then the corresponding -q and -l resource  require‐
              ments  will  be passed to defined JSV instances as parameter
              with the names q_soft and l_soft. Find for informa‐
              tion in the sections describing -q and -l.  (see -jsv option
              above or find more information  concerning  JSV  in
              jsv(1))""")

        if prog in ['qsub']:
            self.parser.add_argument('-sync',
                                     choices=yesno,
                                     help="""\
              Available for qsub.

              -sync  y  causes qsub to wait for the job to complete before exiting.
              If the job completes successfully, qsub's
              exit code will be that of the completed job.
              If the job fails to complete successfully, qsub will print  out  a
              error  message indicating why the job failed and will have an exit code of 1.
              If qsub is interrupted, e.g. with
              CTRL-C, before the job completes, the job will be canceled.
              With the -sync n option, qsub will exit with an exit code of 0 as soon as the
              job  is  submitted  successfully.
              -sync n is default for qsub.
              If  -sync  y is used in conjunction with -now y, qsub will behave
              as though only -now y were given until the job
              has been successfully scheduled, after which time qsub will behave
              as though only -sync y were given.
              If -sync y is used in conjunction with -t n[-m[:i]], qsub will
              wait for all the job's tasks to  complete  before
              exiting.  If all the job's tasks complete successfully, qsub's
              exit code will be that of the first completed job
              tasks with a non-zero exit code, or 0 if all job tasks exited
              with an exit code of 0.  If any of the job's tasks
              fail  to  complete  successfully, qsub will print out an
              error message indicating why the job task(s) failed and
              will have an exit code of 1.  If qsub is interrupted,
              e.g. with CTRL-C, before the job  completes,  all  of  the
              job's tasks will be canceled.

              Information  that  this  switch  was specified during
              submission is not available in the JSV context.  (see -jsv
              option above or find more information concerning JSV in jsv(1))"""
                                     )

        if prog in ['qsub', 'qsh', 'qalter']:
            self.parser.add_argument('-S',
                                     metavar='pathname',
                                     help="""\
       -S [[hostname]:]pathname,...
              Available for qsub, qsh and qalter.

              Specifies the interpreting shell for the job.
              Only one pathname component without a host specifier is valid  and
              only  one path name for a given host is allowed.
              Shell paths with host assignments define the interpreting shell
              for the job if the host is the execution host.
              The shell path without host specification is used if  the  execu‐
              tion host matches none of the hosts in the list.

              Furthermore,  the  pathname  can be constructed with pseudo
              environment variables as described for the -e option
              above.

              In the case of qsh the specified shell path is used to
              execute the  corresponding  command  interpreter  in  the
              xterm(1)  (via its -e option) started on behalf of the interactive job.
              Qalter allows changing this option even
              while the job executes. The modified parameter will only be in effect
              after a restart or migration of  the  job,
              however.

              If  this  option  or  a  corresponding  value in qmon is
              specified then this value will be passed to defined JSV
              instances as parameter with the name S.  (see -jsv option
              above or  find  more  information  concerning  JSV  in
              jsv(1))""")

        if True or prog in ['qsub', 'qalter']:
            self.parser.add_argument('-t',
                                     metavar='n[-m[:s]]',
                                     help="""\
              Available for qsub and qalter only.

              Submits a so called Array Job, i.e. an array of identical
              tasks being differentiated only by an index number and
              being treated by Grid Engine almost like a series of jobs.
              The option argument to -t  specifies  the  number  of
              array job tasks and the index number which will be associated with the tasks.
              The index numbers will be exported
              to the job tasks via the environment variable GE_TASK_ID.
              The option arguments n, m  and  s  will  be  available
              through the environment variables GE_TASK_FIRST,
              GE_TASK_LAST and  GE_TASK_STEPSIZE.

              Following restrictions apply to the values n and m:

                     1 <= n <= MIN(2^31-1, max_aj_tasks)
                     1 <= m <= MIN(2^31-1, max_aj_tasks)
                     n <= m

              max_aj_tasks is defined in the cluster configuration (see sge_conf(5))

              The  task  id range specified in the option argument may be a single
              number, a simple range of the form n-m or a
              range with a step size. Hence, the task id range specified by
              2-10:2 would result in the task id indexes  2,  4,
              6,  8, and 10, for a total of 5 identical tasks, each with
              the environment variable GE_TASK_ID containing one of
              the 5 index numbers.

              All array job tasks inherit the same resource requests and
              attribute definitions as specified  in  the  qsub  or
              qalter  command  line,  except  for  the  -t  option.
              The tasks are scheduled independently and, provided enough
              resources exist, concurrently, very much like separate jobs.
              However, an array job or a sub-array there of  can
              be  accessed  as a single unit by commands like qmod(1) or qdel(1).
              See the corresponding manual pages for fur‐
              ther detail.

              Array jobs are commonly used to execute the same type of operation
              on varying input data  sets  correlated  with
              the task index number. The number of tasks in a array job is unlimited.

              STDOUT and STDERR of array job tasks will be written into different
              files with the default location

              <jobname>.['e'|'o']<job_id>'.'<task_id>

              In order to change this default, the -e and -o options (see above)
              can be used together with the pseudo environ‐
              ment variables $HOME, $USER, $JOB_ID, $JOB_NAME, $HOSTNAME, and $GE_TASK_ID.

              Note, that you can use the output redirection to divert the output
              of all tasks into  the  same  file,  but  the
              result of this is undefined.

              If  this  option  or  a  corresponding  value in qmon is specified
              then this value will be passed to defined JSV
              instances as parameters with the name t_min, t_max and t_step
              (see -jsv option above or  find  more  information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qalter']:
            self.parser.add_argument('-tc',
                                     type=int,
                                     metavar='max_running_tasks',
                                     help="""\
              -allow  users to limit concurrent array job task
              execution. Parameter max_running_tasks specifies maximum number
              of simultaneously running tasks.  For example we have
              running SGE with 10 free slots. We call qsub -t 1-100  -tc
              2 jobscript. Then only 2 tasks will be scheduled to run even
              when 8 slots are free.""")

        if prog in ['qsub']:
            self.parser.add_argument('-terse',
                                     action='store_true',
                                     help="""\
              Available for qsub only.

              -terse  causes  the qsub to display only the job-id of the
              job being submitted rather than the regular "Your job
              ..." string.  In case of an error the error is reported on stderr as usual.
              This can be helpful for scripts which need to parse qsub output to get the job-id.

              Information that this switch was specified during submission
              is not available in the  JSV  context.   (see  -jsv
              option above or find more information concerning JSV in jsv(1))"""
                                     )

        if prog in ['qalter']:
            self.parser.add_argument('-u',
                                     metavar='username',
                                     help="""\
       -u username,...
              Available  for  qalter  only. Changes are only made
              on those jobs which were submitted by users specified in the
              list of usernames.  For managers it is possible to use
              the qalter -u '*' command  to  modify  all  jobs  of  all
              users.

              If you use the -u switch it is not permitted to
              specify an additional wc_job_range_list.""")

        if prog in ['qsub', 'qrsh', 'qalter']:
            self.parser.add_argument('-v',
                                     metavar='variable[=value]',
                                     help="""\
       -v variable[=value],...
              Available for qsub, qrsh (with command argument) and qalter.

              Defines  or  redefines  the environment
              variables to be exported to the execution context of the job.  If the -v
              option is present Grid Engine will add the
              environment variables defined as arguments to the switch and, option‐
              ally, values of specified variables, to the execution context of the job.

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.

              All environment variables specified with -v, -V or the
              DISPLAY variable provided with -display will be  exported
              to the defined JSV instances only optionally when this is
              requested explicitly during the job submission verifi‐
              cation.  (see -jsv option above or find more information concerning JSV in jsv(1))"""
                                     )

        if prog in ['qrsh', 'qmake']:
            self.parser.add_argument('-verbose',
                                     action='store_true',
                                     help="""\
              Available only for qrsh and qmake(1).

              Unlike qsh and qlogin, qrsh does not output any
              informational messages while establishing the session, compliant
              with  the  standard rsh(1) and rlogin(1) system calls.
              If the option -verbose is set, qrsh behaves like the qsh
              and qlogin commands, printing information about the
              process of establishing the rsh(1) or rlogin(1) session.""")

        if prog in ['qsub', 'qrsh', 'qsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-verify',
                                     action='store_true',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter.

              Instead of submitting a job, prints detailed information
              about the would-be job as though qstat(1) -j were used,
              including the effects of command-line parameters and
              the external environment.""")

        if prog in ['qsub', 'qrsh', 'qsh', 'qlogin', 'qalter']:
            # TODO parse acceptability of qrsh argument properly
            self.parser.add_argument('-V',
                                     action='store_true',
                                     help="""\
              Available for qsub, qsh, qrsh with command and qalter.

              Specifies that all environment variables active within
              the qsub utility be exported to the context of the job.

              All  environment variables specified with -v, -V or the DISPLAY
              variable provided with -display will be exported
              to the defined JSV instances only optionally when this is
              requested explicitly during the job submission verifi‐
              cation.  (see -jsv option above or find more information
              concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qsh', 'qlogin', 'qalter']:
            self.parser.add_argument('-w',
                                     choices='ewnpv',
                                     help="""\
              Available for qsub, qsh, qrsh, qlogin and qalter.

              Specifies  a validation level applied to the job to be submitted
              (qsub, qlogin, and qsh) or the specified queued
              job (qalter).  The information displayed indicates whether the
              job can possibly be scheduled assuming  an  empty
              system  with no other jobs. Resource requests exceeding the
              configured maximal thresholds or requesting unavail‐
              able resource attributes are possible causes for jobs to fail this validation.

              The specifiers e, w, n and v define the following validation modes:

              `e'  error - jobs with invalid requests will be
                   rejected.
              `w'  warning - only a warning will be displayed
                   for invalid requests.
              `n'  none - switches off validation; the default for
                   qsub, qalter, qrsh, qsh
                   and qlogin.
              `p'  poke - does not submit the job but prints a
                   validation report based on a cluster as is with
                   all resource utilizations in place.
              `v'  verify - does not submit the job but prints a
                   validation report based on an empty cluster.

              Note, that the necessary checks are performance consuming
              and hence the checking is switched off by default.  It
              should also be noted that load values are not taken
              into account with the verification since they are assumed to
              be too volatile. To cause -w e verification to be passed
              at submission time, it  is  possible  to  specify  non-
              volatile values (non-consumables) or maximum values
              (consumables) in complex_values.""")

        if prog in ['qsub', 'qrsh', 'qsh', 'qalter']:
            self.parser.add_argument('-wd',
                                     metavar='working_dir',
                                     help="""\
              Available for qsub, qsh, qrsh and qalter only.

              Execute  the  job  from  the  directory  specified in working_dir.
              This switch will activate Grid Engine's path
              aliasing facility, if the corresponding configuration files are present
              (see ge_aliases(5)).

              Qalter allows changing this option even while the job executes.
              The modified parameter will only  be  in  effect
              after  a  restart  or  migration  of  the  job,  however.
              The parameter value will be available in defined JSV
              instances as parameter with the name cwd (see -cwd switch above or
              find  more  information  concerning  JSV  in
              jsv(1))""")

        if prog in ['qsub', 'qrsh']:
            self.parser.add_argument('command',
                                     help="""\
              Available for qsub and qrsh only.

              The job's scriptfile or binary.  If not present or if the operand
              is the single-character string '-', qsub reads
              the script from standard input.

              The command will be available in defined JSV instances as parameter
              with the name CMDNAME (see -jsv option above
              or find more information concerning JSV in jsv(1))""")

        if prog in ['qsub', 'qrsh', 'qalter']:
            self.parser.add_argument('command_args',
                                     nargs='*',
                                     help="""\
              Available for qsub, qrsh and qalter only.

              Arguments to the job. Not valid if the script is entered from standard input.

              Qalter  allows  changing  this option even while the job executes.
              The modified parameter will only be in effect
              after a restart or migration of the job, however.

              The number of command arguments is provided to configured
              JSV instances as parameter with the name CMDARGS. Also
              the  argument  values can by accessed. Argument names
              have the format CMDARG<number> where <number> is a integer
              between 0 and CMDARGS - 1.  (see -jsv option above or
              find more information concerning JSV in jsv(1))""")

        if prog in ['qsh']:
            self.parser.add_argument('xterm_args',
                                     nargs='*',
                                     help="""\
              Available for qsh only.

              Arguments to the xterm(1) executable, as defined in the configuration.
              For details, refer to ge_conf(5)).

              Information concerning xterm_args will be available in JSV context as
              parameters  with  the  name  CMDARGS  and
              CMDARG<number>. Find more information above in section command_args.
              (see -jsv option above or find more infor‐
              mation concerning JSV in jsv(1))""")

        # END SGE OPTION PARSER

        # Initialize with defaults
        self.parse('-cwd -V -j y -terse -pe lammpi 1 echo')

    def parse(self, inputstring=''):
        """Helper method: parses a string"""
        return self.parse_args(inputstring.split())

    def parse_args(self, args=None):
        """Helper method: parses a list"""
        if args is None:
            self.args = self.parser.parse_args()  # default is sys.argv[1:]
        else:
            self.args = self.parser.parse_args(args)
        return self.args

    def write_qsub_script(self, filename, echo=False):
        """
        Writes the entire command line to a qsub script

        filename: name of file to write
        echo    : echo contents of script to stdout. Default: False
        """

        buf = ['#!/usr/bin/env qsub', '# Written using SGE module']

        for option, value in self.args.__dict__.items():
            if value is True:
                value = ''

            if option not in ['command', 'command_args', 'xterm_args']:
                if isinstance(value, list):
                    val = ' '.join(value)
                else:
                    val = str(value)

                buf.append(' '.join(['#', '-' + option, val]))

        args = getattr(self.args, 'command_args', [])
        args = getattr(self.args, 'xterm_args', args)

        buf.append(' '.join([self.args.command] + args))

        if echo:
            print('\n'.join(buf))

        f = open(filename, 'w')
        f.write('\n'.join(buf))
        f.close()

    def execute(self, mode='local', path=''):
        """
        Executes qsub

        known modes: local - run locally
                     echo  - echoes out execution string only

        path: path to qsub/... executable: Default = nothing
        """

        # Form execution string

        import random
        test_id = ''
        if "build.log" in self.args.o:
            test_id = self.args.o.split("/")[-2]
        elif "run.log" in self.args.o:
            test_id = self.args.o.split("/")[-3]
        if test_id == '':
            test_id = str(random.randint(1, 9999))

        import os
        program = os.path.join(path, self.prog)
        options = []

        for option, value in self.args.__dict__.items():
            if value is True:
                value = ''

            if isinstance(value, list):
                val = ' '.join(value)
            else:
                val = str(value)

            if option not in ['command', 'command_args', 'xterm_args']:
                options.append('-' + option + ' ' + val)

        args = getattr(self.args, 'command_args', [])
        args = getattr(self.args, 'xterm_args', args)
        # ---------------- command file -------------
        cwd = os.getcwd()
        command_file = cwd + '/command_file_' + str(os.getpid()) + '_' + test_id
        try:
            with open(command_file, 'w') as f_command:
                command_temp = str(self.args.command)
                command_temp = command_temp.replace('"', '')
                f_command.write(command_temp + "\n/bin/rm -f " + command_file)
        except IOError:
            error_msg = 'Error: problem with open File: ' + str(f_command)
            raise IOError(error_msg)

        os.chmod(command_file, 0o0777)
        exestring = ' '.join([program] + options + [command_file] + args)
        exestring = exestring.replace('-pe lammpi 1', '')
        exestring = exestring.replace('-slot', '-pe make')
        exestring = exestring.replace('-ll ', '-l ')
        exestring = exestring.replace('-t 0', '')
        #        exestring = exestring.replace('-j y','')
        print('INFO: sge command file = ' + command_file)
        if mode == 'echo':
            return (exestring)
        elif mode == 'local':
            import subprocess
            p = subprocess.Popen(command_file,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT,
                                 shell=True)
            print(p.stdout.read())


if __name__ == '__main__':
    print('Attempting to validate qsub arguments using argparse')
    o = qsubOptions()
    o.parse_args()
    o.args.t = '1-1000'
    print('I will now print the script')
    o.write_qsub_script('/dev/null', echo=True)
    print('*' * 70)
    print('I will now print the command line')
    o.execute(mode='echo')
