use crate::*;
use libc::c_int;

// libusb_error
pub const LIBUSB_SUCCESS: c_int = 0;
pub const LIBUSB_ERROR_IO: c_int = -1;
pub const LIBUSB_ERROR_INVALID_PARAM: c_int = -2;
pub const LIBUSB_ERROR_ACCESS: c_int = -3;
pub const LIBUSB_ERROR_NO_DEVICE: c_int = -4;
pub const LIBUSB_ERROR_NOT_FOUND: c_int = -5;
pub const LIBUSB_ERROR_BUSY: c_int = -6;
pub const LIBUSB_ERROR_TIMEOUT: c_int = -7;
pub const LIBUSB_ERROR_OVERFLOW: c_int = -8;
pub const LIBUSB_ERROR_PIPE: c_int = -9;
pub const LIBUSB_ERROR_INTERRUPTED: c_int = -10;
pub const LIBUSB_ERROR_NO_MEM: c_int = -11;
pub const LIBUSB_ERROR_NOT_SUPPORTED: c_int = -12;
pub const LIBUSB_ERROR_OTHER: c_int = -99;

// libusb_transfer_status
pub const LIBUSB_TRANSFER_COMPLETED: c_int = 0;
pub const LIBUSB_TRANSFER_ERROR: c_int = 1;
pub const LIBUSB_TRANSFER_TIMED_OUT: c_int = 2;
pub const LIBUSB_TRANSFER_CANCELLED: c_int = 3;
pub const LIBUSB_TRANSFER_STALL: c_int = 4;
pub const LIBUSB_TRANSFER_NO_DEVICE: c_int = 5;
pub const LIBUSB_TRANSFER_OVERFLOW: c_int = 6;

pub const LIBUSB_TRANSFER_SHORT_NOT_OK: u8 = 1 << 0;
pub const LIBUSB_TRANSFER_FREE_BUFFER: u8 = 1 << 1;
pub const LIBUSB_TRANSFER_FREE_TRANSFER: u8 = 1 << 2;
pub const LIBUSB_TRANSFER_ADD_ZERO_PACKET: u8 = 1 << 3;

// libusb_capability
pub const LIBUSB_CAP_HAS_CAPABILITY: u32 = 0x0000;
pub const LIBUSB_CAP_HAS_HOTPLUG: u32 = 0x0001;
pub const LIBUSB_CAP_HAS_HID_ACCESS: u32 = 0x0100;
pub const LIBUSB_CAP_SUPPORTS_DETACH_KERNEL_DRIVER: u32 = 0x0101;

//// libusb_log_level
pub const LIBUSB_LOG_LEVEL_NONE: c_int = 0;
pub const LIBUSB_LOG_LEVEL_ERROR: c_int = 1;
pub const LIBUSB_LOG_LEVEL_WARNING: c_int = 2;
pub const LIBUSB_LOG_LEVEL_INFO: c_int = 3;
pub const LIBUSB_LOG_LEVEL_DEBUG: c_int = 4;

// libusb_class_code
pub const LIBUSB_CLASS_PER_INTERFACE: u8 = 0;
pub const LIBUSB_CLASS_AUDIO: u8 = 1;
pub const LIBUSB_CLASS_COMM: u8 = 2;
pub const LIBUSB_CLASS_HID: u8 = 3;
pub const LIBUSB_CLASS_PHYSICAL: u8 = 5;
pub const LIBUSB_CLASS_PRINTER: u8 = 7;
pub const LIBUSB_CLASS_IMAGE: u8 = 6;
pub const LIBUSB_CLASS_MASS_STORAGE: u8 = 8;
pub const LIBUSB_CLASS_HUB: u8 = 9;
pub const LIBUSB_CLASS_DATA: u8 = 10;
pub const LIBUSB_CLASS_SMART_CARD: u8 = 0x0B;
pub const LIBUSB_CLASS_CONTENT_SECURITY: u8 = 0x0D;
pub const LIBUSB_CLASS_VIDEO: u8 = 0x0E;
pub const LIBUSB_CLASS_PERSONAL_HEALTHCARE: u8 = 0x0F;
pub const LIBUSB_CLASS_DIAGNOSTIC_DEVICE: u8 = 0xDC;
pub const LIBUSB_CLASS_WIRELESS: u8 = 0xE0;
pub const LIBUSB_CLASS_APPLICATION: u8 = 0xFE;
pub const LIBUSB_CLASS_VENDOR_SPEC: u8 = 0xFF;

// libusb_speed
pub const LIBUSB_SPEED_UNKNOWN: c_int = 0;
pub const LIBUSB_SPEED_LOW: c_int = 1;
pub const LIBUSB_SPEED_FULL: c_int = 2;
pub const LIBUSB_SPEED_HIGH: c_int = 3;
pub const LIBUSB_SPEED_SUPER: c_int = 4;
pub const LIBUSB_SPEED_SUPER_PLUS: c_int = 5;

// libusb_descriptor_type
pub const LIBUSB_DT_DEVICE: u8 = 0x01;
pub const LIBUSB_DT_CONFIG: u8 = 0x02;
pub const LIBUSB_DT_STRING: u8 = 0x03;
pub const LIBUSB_DT_INTERFACE: u8 = 0x04;
pub const LIBUSB_DT_ENDPOINT: u8 = 0x05;
pub const LIBUSB_DT_BOS: u8 = 0x0F;
pub const LIBUSB_DT_DEVICE_CAPABILITY: u8 = 0x10;
pub const LIBUSB_DT_HID: u8 = 0x21;
pub const LIBUSB_DT_REPORT: u8 = 0x22;
pub const LIBUSB_DT_PHYSICAL: u8 = 0x23;
pub const LIBUSB_DT_HUB: u8 = 0x29;
pub const LIBUSB_DT_SUPERSPEED_HUB: u8 = 0x2A;
pub const LIBUSB_DT_SS_ENDPOINT_COMPANION: u8 = 0x30;

// libusb_endpoint_direction
pub const LIBUSB_ENDPOINT_ADDRESS_MASK: u8 = 0x0F;
pub const LIBUSB_ENDPOINT_DIR_MASK: u8 = 0x80;
pub const LIBUSB_ENDPOINT_IN: u8 = 0x80;
pub const LIBUSB_ENDPOINT_OUT: u8 = 0x00;

// libusb_transfer_type
pub const LIBUSB_TRANSFER_TYPE_MASK: u8 = 0x03;
pub const LIBUSB_TRANSFER_TYPE_CONTROL: u8 = 0;
pub const LIBUSB_TRANSFER_TYPE_ISOCHRONOUS: u8 = 1;
pub const LIBUSB_TRANSFER_TYPE_BULK: u8 = 2;
pub const LIBUSB_TRANSFER_TYPE_INTERRUPT: u8 = 3;
pub const LIBUSB_TRANSFER_TYPE_BULK_STREAM: u8 = 4;

// libusb_iso_sync_type
pub const LIBUSB_ISO_SYNC_TYPE_MASK: u8 = 0x0C;
pub const LIBUSB_ISO_SYNC_TYPE_NONE: u8 = 0;
pub const LIBUSB_ISO_SYNC_TYPE_ASYNC: u8 = 1;
pub const LIBUSB_ISO_SYNC_TYPE_ADAPTIVE: u8 = 2;
pub const LIBUSB_ISO_SYNC_TYPE_SYNC: u8 = 3;

// libusb_iso_usage_type
pub const LIBUSB_ISO_USAGE_TYPE_MASK: u8 = 0x30;
pub const LIBUSB_ISO_USAGE_TYPE_DATA: u8 = 0;
pub const LIBUSB_ISO_USAGE_TYPE_FEEDBACK: u8 = 1;
pub const LIBUSB_ISO_USAGE_TYPE_IMPLICIT: u8 = 2;

// libusb_request_type
pub const LIBUSB_REQUEST_TYPE_STANDARD: u8 = 0x00 << 5;
pub const LIBUSB_REQUEST_TYPE_CLASS: u8 = 0x01 << 5;
pub const LIBUSB_REQUEST_TYPE_VENDOR: u8 = 0x02 << 5;
pub const LIBUSB_REQUEST_TYPE_RESERVED: u8 = 0x03 << 5;

// libusb_request_recipient
pub const LIBUSB_RECIPIENT_DEVICE: u8 = 0x00;
pub const LIBUSB_RECIPIENT_INTERFACE: u8 = 0x01;
pub const LIBUSB_RECIPIENT_ENDPOINT: u8 = 0x02;
pub const LIBUSB_RECIPIENT_OTHER: u8 = 0x03;

// libusb_standard_request
pub const LIBUSB_REQUEST_GET_STATUS: u8 = 0x00;
pub const LIBUSB_REQUEST_CLEAR_FEATURE: u8 = 0x01;
pub const LIBUSB_REQUEST_SET_FEATURE: u8 = 0x03;
pub const LIBUSB_REQUEST_SET_ADDRESS: u8 = 0x05;
pub const LIBUSB_REQUEST_GET_DESCRIPTOR: u8 = 0x06;
pub const LIBUSB_REQUEST_SET_DESCRIPTOR: u8 = 0x07;
pub const LIBUSB_REQUEST_GET_CONFIGURATION: u8 = 0x08;
pub const LIBUSB_REQUEST_SET_CONFIGURATION: u8 = 0x09;
pub const LIBUSB_REQUEST_GET_INTERFACE: u8 = 0x0A;
pub const LIBUSB_REQUEST_SET_INTERFACE: u8 = 0x0B;
pub const LIBUSB_REQUEST_SYNCH_FRAME: u8 = 0x0C;
pub const LIBUSB_REQUEST_SET_SEL: u8 = 0x30;
pub const LIBUSB_SET_ISOCH_DELAY: u8 = 0x31;

// libusb_hotplug
pub const LIBUSB_HOTPLUG_NO_FLAGS: c_int = 0;
pub const LIBUSB_HOTPLUG_ENUMERATE: c_int = 1 << 0;
pub const LIBUSB_HOTPLUG_EVENT_DEVICE_ARRIVED: c_int = 0x01;
pub const LIBUSB_HOTPLUG_EVENT_DEVICE_LEFT: c_int = 0x02;
pub const LIBUSB_HOTPLUG_MATCH_ANY: c_int = -1;

pub const LIBUSB_OPTION_LOG_LEVEL: u32 = 0x00;
pub const LIBUSB_OPTION_USE_USBDK: u32 = 0x01;
pub const LIBUSB_OPTION_WEAK_AUTHORITY: u32 = 0x02;
pub const LIBUSB_OPTION_NO_DEVICE_DISCOVERY: u32 = 0x02;

// libusb_log_cb_mode
pub const LIBUSB_LOG_CB_GLOBAL: libusb_log_cb_mode = 1 << 0;
pub const LIBUSB_LOG_CB_CONTEXT: libusb_log_cb_mode = 1 << 1;

pub const LIBUSB_CONTROL_SETUP_SIZE: usize = std::mem::size_of::<libusb_control_setup>();
