from struct import pack, unpack


def pack_list(data: list):
    bytes = b""
    for item in data:
        bytes += pack("Q", item & ((1 << 64) - 1))
        bytes += pack("Q", (item >> 64) & ((1 << 64) - 1))
        bytes += pack("Q", (item >> 128) & ((1 << 64) - 1))
        bytes += pack("Q", (item >> 192) & ((1 << 64) - 1))
    return bytes


def unpack_list(bytes):
    data = []
    words = int(len(bytes) / 32)
    for word in range(words):
        result = 0
        for i in range(3, -1, -1):
            result <<= 64
            barray = bytes[word * 32 + i * 8:word * 32 + i * 8 + 8]
            result += unpack("Q", barray)[0]
        data.append(result)
    return data
