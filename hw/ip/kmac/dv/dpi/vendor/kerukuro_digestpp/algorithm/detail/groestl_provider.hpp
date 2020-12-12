/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_GROESTL_HPP
#define DIGESTPP_PROVIDERS_GROESTL_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/groestl_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace groestl_functions
{
	template<int R>
	static inline void roundP(uint64_t* x, uint64_t* y, uint64_t i)
	{
	   for (int idx = 0; idx < R; idx++)
		   x[idx] ^= (static_cast<uint64_t>(idx) << 4) ^ i;

	   for (int c = R - 1; c >= 0; c--)
		   y[c] = groestl_constants<void>::T[0][static_cast<unsigned char>(x[(c + 0) % R])]
			   ^ groestl_constants<void>::T[1][static_cast<unsigned char>(x[(c + 1) % R] >> 8)]
			   ^ groestl_constants<void>::T[2][static_cast<unsigned char>(x[(c + 2) % R] >> 16)]
			   ^ groestl_constants<void>::T[3][static_cast<unsigned char>(x[(c + 3) % R] >> 24)]
			   ^ groestl_constants<void>::T[4][static_cast<unsigned char>(x[(c + 4) % R] >> 32)]
			   ^ groestl_constants<void>::T[5][static_cast<unsigned char>(x[(c + 5) % R] >> 40)]
			   ^ groestl_constants<void>::T[6][static_cast<unsigned char>(x[(c + 6) % R] >> 48)]
			   ^ groestl_constants<void>::T[7][static_cast<unsigned char>(x[(c + (R == 16 ? 11 : 7)) % R] >> 56)];
	}

	template<int R>
	static inline void roundQ(uint64_t* x, uint64_t* y, uint64_t i)
	{
	   for (int idx = 0; idx < R; idx++)
		   x[idx] ^= (0xffffffffffffffffull - (static_cast<uint64_t>(idx) << 60)) ^ i;

	   for (int c = R - 1; c >= 0; c--)
		   y[c] = groestl_constants<void>::T[0][static_cast<unsigned char>(x[(c + 1) % R])]
			   ^ groestl_constants<void>::T[1][static_cast<unsigned char>(x[(c + 3) % R] >> 8)]
			   ^ groestl_constants<void>::T[2][static_cast<unsigned char>(x[(c + 5) % R] >> 16)]
			   ^ groestl_constants<void>::T[3][static_cast<unsigned char>(x[(c + (R == 16 ? 11 : 7)) % R] >> 24)]
			   ^ groestl_constants<void>::T[4][static_cast<unsigned char>(x[(c + 0) % R] >> 32)]
			   ^ groestl_constants<void>::T[5][static_cast<unsigned char>(x[(c + 2) % R] >> 40)]
			   ^ groestl_constants<void>::T[6][static_cast<unsigned char>(x[(c + 4) % R] >> 48)]
			   ^ groestl_constants<void>::T[7][static_cast<unsigned char>(x[(c + 6) % R] >> 56)];
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
			roundQ<R>(AQ1, AQ2, r << 56);
			roundQ<R>(AQ2, AQ1, (r + 1ull) << 56);
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

class groestl_provider
{
public:
	static const bool is_xof = false;

	groestl_provider(size_t hashsize)
		: hs(hashsize)
	{
		validate_hash_size(hashsize, 512);
	}

	~groestl_provider()
	{
		clear();
	}

	inline void init()
	{
		pos = 0;
		total = 0;
		memset(&h[0], 0, sizeof(uint64_t)*16);
		uint64_t hs = hash_size();
		h[hs > 256 ? 15 : 7] = byteswap(hs);
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, block_bytes(), block_bytes(), m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len); });
	}

	inline void final(unsigned char* hash)
	{
		m[pos++] = 0x80;
		total += pos * 8;
		size_t limit = block_bytes();
		if (pos > limit - 8)
		{
			if (limit != pos)
				memset(&m[pos], 0, limit - pos);
			transform(m.data(), 1);
			total += (block_bytes() - pos) * 8;
			pos = 0;
		}
		memset(&m[pos], 0, limit - 8 - pos);
		total += (block_bytes() - pos) * 8;
		uint64_t mlen = byteswap(total / 8 / block_bytes());
		memcpy(&m[limit - 8], &mlen, 64 / 8);
		transform(m.data(), 1);
		outputTransform();

		const unsigned char* s = reinterpret_cast<const unsigned char*>(h.data());
		for (size_t i = limit - hash_size() / 8, j = 0; i < limit; i++, j++) {
			hash[j] = s[i];
		}
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
			groestl_functions::outputTransform<16>(&h[0]);
		else
			groestl_functions::outputTransform<8>(&h[0]);
	}

	inline void transform(const unsigned char* mp, size_t num_blks)
	{
		for (size_t blk = 0; blk < num_blks; blk++)
		{
			if (hs > 256)
				groestl_functions::transform<16>(&h[0], reinterpret_cast<const uint64_t*>(mp + block_bytes() * blk));
			else
				groestl_functions::transform<8>(&h[0], reinterpret_cast<const uint64_t*>(mp + block_bytes() * blk));
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