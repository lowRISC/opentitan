#include <iostream>
#include <string>

#include "cxxopts.hpp"
#include "serial/serial.h"

int main(int argc, const char** argv) {
  cxxopts::Options options("test", "A brief description");

  options.add_options()("p,port", "Serial port to connect to",
                        cxxopts::value<std::string>())(
      "b,baudrate", "Baudrate of the serial connection",
      cxxopts::value<uint32_t>()->default_value("115200"))(
      "s,success_on_string",
      "Return a successful return code if this string is sent over serial",
      cxxopts::value<std::string>()->default_value(""))(
      "f,fail_on_string",
      "Return an unsuccesful return code if this string is sent over serial",
      cxxopts::value<std::string>()->default_value(""))("h,help",
                                                        "Print usage");

  auto result = options.parse(argc, argv);

  if (result.count("help")) {
    std::cout << options.help() << std::endl;
    exit(0);
  }
  std::string port;
  if (result.count("port")) {
    port = result["port"].as<std::string>();
  } else {
    std::cout << options.help() << std::endl;
    exit(1);
  }
  uint32_t baudrate = result["baudrate"].as<uint32_t>();
  std::string success_on_string = result["success_on_string"].as<std::string>();
  std::string fail_on_string = result["fail_on_string"].as<std::string>();
  serial::Serial serial_out(port, baudrate,
                            serial::Timeout::simpleTimeout(1000));
  while (1) {
    try {
      std::string buffer;
      serial_out.readline(buffer);
      if (!buffer.empty()) {
        std::cout << buffer << "\n";
      }
      if (buffer.find(success_on_string) != std::string::npos &&
          !success_on_string.empty()) {
        exit(0);
      }
      if (buffer.find(fail_on_string) != std::string::npos &&
          !fail_on_string.empty()) {
        exit(2);
      }
    } catch (serial::PortNotOpenedException e) {
      std::cerr << "Port:" << port << ", could not be opened\n";
      exit(1);
    } catch (serial::SerialException) {
      std::cerr << "An unknown exception occured with serial communication "
                   "exiting...\n";
      exit(1);
    }
  }
  return 0;
}