<%
clks_attr = cfg['clocks']
grps = clks_attr['groups']
num_hints = len(hint_clks)
%>

package clkmgr_pkg;

  typedef struct packed {
    logic test_en;
  } clk_dft_t;

  parameter clk_dft_t CLK_DFT_DEFAULT = '{
    test_en: 1'b0
  };

  typedef struct packed {
% for clk in {**hint_clks, **rg_clks, **sw_clks}:
  logic ${clk};
% endfor

  } clkmgr_out_t;

  typedef struct packed {
    logic [${num_hints}-1:0] idle;
  } clk_hint_status_t;

  parameter clk_hint_status_t CLK_HINT_STATUS_DEFAULT = '{
    idle: {${num_hints}{1'b1}}
  };


endpackage // clkmgr_pkg
