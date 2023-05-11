LIBUSB_DIR=/home/adrianl/Exps/libusb-master
g++ -c -o usb_suspend_test.o -I${LIBUSB_DIR}/libusb usb_suspend_test.cc
${LIBUSB_DIR}/libtool --silent --tag=CC   --mode=link g++ -std=c++14  -Wall -Wextra -Wshadow -Wunused -Wwrite-strings -Werror=format-security -Werror=implicit-function-declaration -Werror=implicit-int -Werror=init-self -Werror=missing-prototypes -Werror=strict-prototypes -Werror=undef -Werror=uninitialized -g -O2 -o usb_suspend_test usb_suspend_test.o ${LIBUSB_DIR}/libusb/libusb-1.0.la
