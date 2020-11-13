/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_KUPYNA_HPP
#define DIGESTPP_PROVIDERS_KUPYNA_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/kupyna_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace kupyna_functions
{
	template<int R>
	static inline void G(uint64_t* x, uint64_t* y)
	{
	   for (int c = 0; c != R; ++c)
		   y[c] = kupyna_constants<void>::T[0][static_cast<unsigned char>(x[(c + R) % R])]
			   ^ kupyna_constants<void>::T[1][static_cast<unsigned char>(x[(c + R - 1) % R] >> 8)]
			   ^ kupyna_constants<void>::T[2][static_cast<unsigned char>(x[(c + R - 2) % R] >> 16)]
			   ^ kupyna_constants<void>::T[3][static_cast<unsigned char>(x[(c + R - 3) % R] >> 24)]
			   ^ kupyna_constants<void>::T[4][static_cast<unsigned char>(x[(c + R - 4) % R] >> 32)]
			   ^ kupyna_constants<void>::T[5][static_cast<unsigned char>(x[(c + R - 5) % R] >> 40)]
			   ^ kupyna_constants<void>::T[6][static_cast<unsigned char>(x[(c + R - 6) % R] >> 48)]
			   ^ kupyna_constants<void>::T[7][static_cast<unsigned char>(x[(c + R - (R == 16 ? 11 : 7)) % R] >> 56)];
	}

	template<int R>
	static inline void roundP(uint64_t* x, uint64_t* y, uint64_t i)
	{
	   for (int idx = 0; idx < R; idx++)
		   x[idx] ^= (static_cast<uint64_t>(idx) << 4) ^ i;

	   G<R>(x, y);
	}

	template<int R>
	static inline void roundQ(uint64_t* x, uint64_t* y, uint64_t i)
	{
		for (int j = 0; j < R; ++j)
			x[j] += (0x00F0F0F0F0F0F0F3ULL
					^ ((static_cast<uint64_t>(((R - 1 - j) * 0x10) ^ static_cast<unsigned char>(i))) << 56));

	   G<R>(x, y);
	}

	template<int R>
	static inline void transform(uint64_t* h, const uint64_t* m)
	{
		uint64_t AQ1[R], AQ2[R], AP1[R], AP2[R];

		for (int column = 0; column < R; column++)
		{
			AP1[column] = h[column] ^ m[column];
			AQ1[column] = m[column];
		}

		for (uint64_t r = 0; r < (R == 16 ? 14 : 10); r += 2)
		{
			roundP<R>(AP1, AP2, r);
			roundP<R>(AP2, AP1, r + 1);
			roundQ<R>(AQ1, AQ2, r);
			roundQ<R>(AQ2, AQ1, r + 1);
		}

		for (int column = 0; column < R; column++)
		{
			h[column] = AP1[column] ^ AQ1[column] ^ h[column];
		}
	}

	template<int R>
	static inline void outputTransform(uint64_t* h)
	{
		uint64_t t1[R];
		uint64_t t2[R];

		for (int column = 0; column < R; column++) {
			t1[column] = h[column];
		}

		for (uint64_t r = 0; r < (R == 16 ? 14 : 10); r += 2) {
			roundP<R>(t1, t2, r);
			roundP<R>(t2, t1, r+1);
		}

		for (int column = 0; column < R; column++) {
			h[column] ^= t1[column];
		}
	}

}

class kupyna_provider
{
public:
	static const bool is_xof = false;

	kupyna_provider(size_t hashsize)
		: hs(hashsize)
	{
		validate_hash_size(hashsize, { 256, 512 });
	}

	~kupyna_provider()
	{
		clear();
	}

	inline void init()
	{
		pos = 0;
		total = 0;
		memset(&h[0], 0, sizeof(uint64_t)*16);
		h[0] = block_bytes(); // state in bytes
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, block_bytes(), block_bytes(), m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len); });
	}

	inline void final(unsigned char* hash)
	{
		total += pos * 8;
		m[pos++] = 0x80;
		size_t limit = block_bytes();
		if (pos > limit - 12)
		{
			if (limit != pos)
				memset(&m[pos], 0, limit - pos);
			transform(m.data(), 1);
			pos = 0;
		}
		memset(&m[pos], 0, limit - pos);
		memcpy(&m[limit - 12], &total, sizeof(uint64_t));
		memset(&m[limit - 4], 0, 4);

		transform(m.data(), 1);
		outputTransform();

		memcpy(hash, reinterpret_cast<const unsigned char*>(h.data()) + limit - hash_size() / 8, hash_size() / 8);
	}

	inline void clear()
	{
		zero_memory(h);
		zero_memory(m);
	}

	inline size_t hash_size() const { return hs; }

private:
	inline size_t block_bytes() const { return hs > 256 ? 128 : 64; }

	inline void outputTransform()
	{
		if (hs > 256)
			kupyna_functions::outputTransform<16>(&h[0]);
		else
			kupyna_functions::outputTransform<8>(&h[0]);
	}

	inline void transform(const unsigned char* mp, size_t num_blks)
	{
		for (size_t blk = 0; blk < num_blks; blk++)
		{
			if (hs > 256)
				kupyna_functions::transform<16>(&h[0], reinterpret_cast<const uint64_t*>(mp + block_bytes() * blk));
			else
				kupyna_functions::transform<8>(&h[0], reinterpret_cast<const uint64_t*>(mp + block_bytes() * blk));
		}
	}

	std::array<uint64_t, 16> h;
	std::array<unsigned char, 128> m;
	size_t hs;
	size_t pos;
	uint64_t total;

};

} // namespace detail

} // namespace digestpp

#endif