{
  name: "${name}"
  // TODO: remove the common testplans if not applicable
  import_testplans: ["hw/dv/tools/testplans/csr_testplan.hjson",
                     "hw/dv/tools/testplans/mem_testplan.hjson",
                     "hw/dv/tools/testplans/intr_test_testplan.hjson",
                     "hw/dv/tools/testplans/tl_device_access_types_testplan.hjson"]
  entries: [
    {
      name: sanity
      desc: '''**Goal**: Basic sanity test acessing a major datapath in ${name.upper()}.

            **Stimulus**: Describe the stimulus procedure.

            **Checks**": Describe the self-check procedure.
            - add bullets as needed
            - second bullet<br>
              describe second bullet

            Start a new paragraph.'''
      milestone: v1
      tests: ["${name}_sanity"]
    }
    {
      name: feature1
      desc: '''Add more test entries here like above.'''
      milestone: v1
      tests: []
    }
  ]
}
