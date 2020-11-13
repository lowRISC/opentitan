/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_MD5_HPP
#define DIGESTPP_PROVIDERS_MD5_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "constants/md5_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace md5_functions
{
	static inline void roundf(int round, uint32_t& a, uint32_t& b, uint32_t& c, uint32_t& d, const uint32_t* M)
	{
		a = b + rotate_left(a + (d ^ (b & (c ^ d))) + md5_constants<void>::K[round] + M[round],
				md5_constants<void>::S[round]);
	}

	static inline void roundg(int round, uint32_t& a, uint32_t& b, uint32_t& c, uint32_t& d, const uint32_t* M)
	{
		a = b + rotate_left(a + (c ^ (d & (b ^ c))) + md5_constants<void>::K[round] + M[(5 * round + 1) % 16],
				md5_constants<void>::S[round]);
	}

	static inline void roundh(int round, uint32_t& a, uint32_t& b, uint32_t& c, uint32_t& d, const uint32_t* M)
	{
		a = b + rotate_left(a + (b ^ c ^ d) + md5_constants<void>::K[round] + M[(3 * round + 5) % 16],
				md5_constants<void>::S[round]);
	}

	static inline void roundi(int round, uint32_t& a, uint32_t& b, uint32_t& c, uint32_t& d, const uint32_t* M)
	{
		a = b + rotate_left(a + (c ^ (b | ~d)) + md5_constants<void>::K[round] + M[(7 * round) % 16],
				md5_constants<void>::S[round]);
	}

}

class md5_provider
{
public:
	static const bool is_xof = false;

	md5_provider()
	{
	}

	~md5_provider()
	{
		clear();
	}

	inline void init()
	{
		H[0] = 0x67452301;
		H[1] = 0xefcdab89;
		H[2] = 0x98badcfe;
		H[3] = 0x10325476;
		pos = 0;
		total = 0;
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, 64, 64, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len); });
	}

	inline void final(unsigned char* hash)
	{
		total += pos * 8;
		m[pos++] = 0x80;
		if (pos > 56)
		{
			if (pos != 64)
				memset(&m[pos], 0, 64 - pos);
			transform(&m[0], 1);
			pos = 0;
		}
		memset(&m[0] + pos, 0, 56 - pos);
		memcpy(&m[0] + (64 - 8), &total, 64 / 8);
		transform(&m[0], 1);
		memcpy(hash, H.data(), 16);
	}

	inline void clear()
	{
		zero_memory(H);
		zero_memory(m);
	}

	inline size_t hash_size() const { return 128; }

private:
	inline void transform(const unsigned char* data, size_t num_blks)
	{
		const uint32_t* M = reinterpret_cast<const uint32_t*>(data);
		for (uint64_t blk = 0; blk < num_blks; blk++, M += 16)
		{
			uint32_t a = H[0];
			uint32_t b = H[1];
			uint32_t c = H[2];
			uint32_t d = H[3];

			md5_functions::roundf(0, a, b, c, d, M);
			md5_functions::roundf(1, d, a, b, c, M);
			md5_functions::roundf(2, c, d, a, b, M);
			md5_functions::roundf(3, b, c, d, a, M);
			md5_functions::roundf(4, a, b, c, d, M);
			md5_functions::roundf(5, d, a, b, c, M);
			md5_functions::roundf(6, c, d, a, b, M);
			md5_functions::roundf(7, b, c, d, a, M);
			md5_functions::roundf(8, a, b, c, d, M);
			md5_functions::roundf(9, d, a, b, c, M);
			md5_functions::roundf(10, c, d, a, b, M);
			md5_functions::roundf(11, b, c, d, a, M);
			md5_functions::roundf(12, a, b, c, d, M);
			md5_functions::roundf(13, d, a, b, c, M);
			md5_functions::roundf(14, c, d, a, b, M);
			md5_functions::roundf(15, b, c, d, a, M);

			md5_functions::roundg(16, a, b, c, d, M);
			md5_functions::roundg(17, d, a, b, c, M);
			md5_functions::roundg(18, c, d, a, b, M);
			md5_functions::roundg(19, b, c, d, a, M);
			md5_functions::roundg(20, a, b, c, d, M);
			md5_functions::roundg(21, d, a, b, c, M);
			md5_functions::roundg(22, c, d, a, b, M);
			md5_functions::roundg(23, b, c, d, a, M);
			md5_functions::roundg(24, a, b, c, d, M);
			md5_functions::roundg(25, d, a, b, c, M);
			md5_functions::roundg(26, c, d, a, b, M);
			md5_functions::roundg(27, b, c, d, a, M);
			md5_functions::roundg(28, a, b, c, d, M);
			md5_functions::roundg(29, d, a, b, c, M);
			md5_functions::roundg(30, c, d, a, b, M);
			md5_functions::roundg(31, b, c, d, a, M);

			md5_functions::roundh(32, a, b, c, d, M);
			md5_functions::roundh(33, d, a, b, c, M);
			md5_functions::roundh(34, c, d, a, b, M);
			md5_functions::roundh(35, b, c, d, a, M);
			md5_functions::roundh(36, a, b, c, d, M);
			md5_functions::roundh(37, d, a, b, c, M);
			md5_functions::roundh(38, c, d, a, b, M);
			md5_functions::roundh(39, b, c, d, a, M);
			md5_functions::roundh(40, a, b, c, d, M);
			md5_functions::roundh(41, d, a, b, c, M);
			md5_functions::roundh(42, c, d, a, b, M);
			md5_functions::roundh(43, b, c, d, a, M);
			md5_functions::roundh(44, a, b, c, d, M);
			md5_functions::roundh(45, d, a, b, c, M);
			md5_functions::roundh(46, c, d, a, b, M);
			md5_functions::roundh(47, b, c, d, a, M);

			md5_functions::roundi(48, a, b, c, d, M);
			md5_functions::roundi(49, d, a, b, c, M);
			md5_functions::roundi(50, c, d, a, b, M);
			md5_functions::roundi(51, b, c, d, a, M);
			md5_functions::roundi(52, a, b, c, d, M);
			md5_functions::roundi(53, d, a, b, c, M);
			md5_functions::roundi(54, c, d, a, b, M);
			md5_functions::roundi(55, b, c, d, a, M);
			md5_functions::roundi(56, a, b, c, d, M);
			md5_functions::roundi(57, d, a, b, c, M);
			md5_functions::roundi(58, c, d, a, b, M);
			md5_functions::roundi(59, b, c, d, a, M);
			md5_functions::roundi(60, a, b, c, d, M);
			md5_functions::roundi(61, d, a, b, c, M);
			md5_functions::roundi(62, c, d, a, b, M);
			md5_functions::roundi(63, b, c, d, a, M);

			H[0] += a;
			H[1] += b;
			H[2] += c;
			H[3] += d;
		}
	}

	std::array<uint32_t, 4> H;
	std::array<unsigned char, 64> m;
	size_t pos;
	uint64_t total;
};

} // namespace detail

} // namespace digestpp

#endif