// this interface class is a catalog of general memory functions that the programmer
// must implement according to each memory type they choose to use
interface class gen_mem_base_if;
    pure virtual function automatic logic [7:0] read8(input bit [bus_params_pkg::BUS_AW-1:0] addr);

    pure virtual function automatic logic [15:0] read16(input bit [bus_params_pkg::BUS_AW-1:0] addr);

    pure virtual function automatic logic [31:0] read32(input bit [bus_params_pkg::BUS_AW-1:0] addr);

    pure virtual function automatic logic [63:0] read64(input bit [bus_params_pkg::BUS_AW-1:0] addr);

    pure virtual function automatic void write8(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                input bit [7:0] data,
                                                input int inject_num_errors = 0);

    pure virtual function automatic void write16(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                input bit [15:0] data,
                                                input int inject_num_errors = 0);

    pure virtual function automatic void write32(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                input bit [31:0] data,
                                                input int inject_num_errors = 0);

    pure virtual function automatic void write64(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                input bit [63:0] data,
                                                input int inject_num_errors = 0);

    // iniatialize paramaters of the interface if needed
    pure virtual function automatic void init();

    pure virtual function automatic bit is_addr_valid(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    
    pure virtual function automatic void clear_mem();

    pure virtual function automatic void set_mem();

    pure virtual function automatic void load_mem_from_file(string file);

    pure virtual function automatic void write_mem_to_file(string file);

    pure virtual function automatic void randomize_mem();

    pure virtual function automatic void invalidate_mem();
endclass : gen_mem_base_if