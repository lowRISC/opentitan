// this interface class is a catalog of OTP specific functions that the programmer
// must implement
interface class otp_mem_base_if;
    pure virtual function automatic secded_22_16_t ecc_read16(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    pure virtual function automatic secded_39_32_t ecc_read32(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    pure virtual function automatic secded_72_64_t ecc_read64(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    pure virtual function automatic bit [MAX_WIDTH-1:0] inject_errors(bit [MAX_WIDTH-1:0] data, int inject_num_errors);
endclass