//  Class: mem_bkdr_base_if
// 
// this class is not a pure virtual class, but doesn't actually implement anything
// concrete implementation is left for the vendor/PRIM_GENERIC implementation in
// the classes inside the implementation-specific interface
class otp_bkdr_base_if extends uvm_component implements gen_mem_base_if, otp_mem_base_if;
    `uvm_component_utils(otp_bkdr_base_if);

               
    ////////////////////////////////////////////////////////////////////
    ///////////////////  gen_mem_base_if implementations  //////////////
    ////////////////////////////////////////////////////////////////////
    function new(string name = "otp_bkdr_base_if", uvm_component parent);
        super.new(name, parent);
    endfunction: new
                                          
    virtual function automatic void init();
        `uvm_error(get_full_name(), "init is not implemented!")
    endfunction

    virtual function automatic bit is_addr_valid(input bit [bus_params_pkg::BUS_AW-1:0] addr);
        `uvm_error(get_full_name(), "is_addr_valid is not implemented!")
    endfunction

    virtual function automatic logic [7:0] read8(input bit [bus_params_pkg::BUS_AW-1:0] addr);
        `uvm_error(get_full_name(), "read8 is not implemented!")
    endfunction 

    virtual function automatic logic [15:0] read16(input bit [bus_params_pkg::BUS_AW-1:0] addr);
        `uvm_error(get_full_name(), "read16 is not implemented!")
    endfunction 

    virtual function automatic logic [31:0] read32(input bit [bus_params_pkg::BUS_AW-1:0] addr);
        `uvm_error(get_full_name(), "read32 is not implemented!")
    endfunction 

    virtual function automatic logic [63:0] read64(input bit [bus_params_pkg::BUS_AW-1:0] addr);
        `uvm_error(get_full_name(), "read64 is not implemented!")
    endfunction 

    virtual function automatic void write8(  input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                    input bit [7:0] data,
                                                    input int inject_num_errors = 0);
        `uvm_error(get_full_name(), "write8 is not implemented!")
    endfunction 

    virtual function automatic void write16(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                    input bit [15:0] data,
                                                    input int inject_num_errors = 0);
        `uvm_error(get_full_name(), "write16 is not implemented!")
    endfunction 

    virtual function automatic void write32(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                    input bit [31:0] data,
                                                    input int inject_num_errors = 0);
        `uvm_error(get_full_name(), "write32 is not implemented!")
    endfunction 

    virtual function automatic void write64(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                    input bit [63:0] data,
                                                    input int inject_num_errors = 0);
        `uvm_error(get_full_name(), "write64 is not implemented!")
    endfunction 
   
    // check if input file is read/writable
    virtual function automatic void check_file(string file, bit wr);
        `uvm_error(get_full_name(), "check_file is not implemented!")
    endfunction

    // load mem from file
    virtual function automatic void load_mem_from_file(string file);
        `uvm_error(get_full_name(), "load_mem_from_file is not implemented!")
    endfunction

    // save mem contents to file
    virtual function automatic void write_mem_to_file(string file);
        `uvm_error(get_full_name(), "write_mem_to_file is not implemented!")
    endfunction

    // print mem
    virtual function automatic void print_mem();
        `uvm_error(get_full_name(), "print_mem is not implemented!")
    endfunction

    // clear or set memory
    virtual function automatic void clear_mem();
        `uvm_error(get_full_name(), "clear_mem is not implemented!")
    endfunction // clr_mem

    virtual function automatic void set_mem();
        `uvm_error(get_full_name(), "set_mem is not implemented!")
    endfunction

    // randomize the memory
    virtual function automatic void randomize_mem();
        `uvm_error(get_full_name(), "randomize_mem is not implemented!")
    endfunction

    // invalidate the memory.
    virtual function automatic void invalidate_mem();
        `uvm_error(get_full_name(), "invalidate_mem is not implemented!")
    endfunction

    ////////////////////////////////////////////////////////////////////
    ///////////////////  otp_mem_base_if implementations  //////////////
    ////////////////////////////////////////////////////////////////////
    virtual function automatic secded_22_16_t ecc_read16(input bit [bus_params_pkg::BUS_AW-1:0] addr);
        `uvm_error(get_full_name(), "ecc_read16 is not implemented!")
    endfunction

    // Intended for use with memories which have data width of 32 bits and 7 ECC bits.
    virtual function automatic secded_39_32_t ecc_read32(input bit [bus_params_pkg::BUS_AW-1:0] addr);
        `uvm_error(get_full_name(), "ecc_read32 is not implemented!")
    endfunction

    // Intended for use with memories which have data width of 64 bits and 8 ECC bits.
    virtual function automatic secded_72_64_t ecc_read64(input bit [bus_params_pkg::BUS_AW-1:0] addr);
        `uvm_error(get_full_name(), "ecc_read64 is not implemented!")
    endfunction

    virtual function automatic bit [MAX_WIDTH-1:0] inject_errors(bit [MAX_WIDTH-1:0] data, int inject_num_errors);
        `uvm_error(get_full_name(), "inject_errors is not implemented!")
    endfunction

        
endclass: otp_bkdr_base_if
