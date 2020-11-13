/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_BLAKE_HPP
#define DIGESTPP_PROVIDERS_BLAKE_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/blake_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace blake_functions
{
	static inline void G(int r, int i, uint32_t& a, uint32_t& b, uint32_t& c, uint32_t& d, uint32_t* M)
	{
		a = a + b + (M[blake_constants<void>::S[r % 10][2 * i]]
				^ blake_constants<void>::c[blake_constants<void>::S[r % 10][2 * i + 1]]);
		d = rotate_right(d ^ a, 16);
		c = c + d;
		b = rotate_right(b ^ c, 12);
		a = a + b + (M[blake_constants<void>::S[r % 10][2 * i + 1]]
				^ blake_constants<void>::c[blake_constants<void>::S[r % 10][2 * i]]);
		d = rotate_right(d ^ a, 8);
		c = c + d;
		b = rotate_right(b ^ c, 7);
	}

	static inline void G(int r, int i, uint64_t& a, uint64_t& b, uint64_t& c, uint64_t& d, uint64_t* M)
	{
		a = a + b + (M[blake_constants<void>::S[r % 10][2 * i]]
				^ blake_constants<void>::c512[blake_constants<void>::S[r % 10][2 * i + 1]]);
		d = rotate_right(d ^ a, 32);
		c = c + d;
		b = rotate_right(b ^ c, 25);
		a = a + b + (M[blake_constants<void>::S[r % 10][2 * i + 1]]
				^ blake_constants<void>::c512[blake_constants<void>::S[r % 10][2 * i]]);
		d = rotate_right(d ^ a, 16);
		c = c + d;
		b = rotate_right(b ^ c, 11);
	}

	template<typename T>
	static inline void round(int r, T* M, T* v)
	{
		G(r, 0, v[0], v[4], v[8], v[12], M);
		G(r, 1, v[1], v[5], v[9], v[13], M);
		G(r, 2, v[2], v[6], v[10], v[14], M);
		G(r, 3, v[3], v[7], v[11], v[15], M);
		G(r, 4, v[0], v[5], v[10], v[15], M);
		G(r, 5, v[1], v[6], v[11], v[12], M);
		G(r, 6, v[2], v[7], v[8], v[13], M);
		G(r, 7, v[3], v[4], v[9], v[14], M);
	}

	template<typename T>
	inline T C(int t);

	template<>
	inline uint32_t C<uint32_t>(int t)
	{
		return blake_constants<void>::c[t];
	}

	template<>
	inline uint64_t C<uint64_t>(int t)
	{
		return blake_constants<void>::c512[t];
	}

	template<typename T>
	inline void transform(const unsigned char* data, size_t num_blks, bool padding, std::array<T, 12>& H, uint64_t total, bool final)
	{
		for (size_t blk = 0; blk < num_blks; blk++)
		{
			T M[16];
			for (int i = 0; i < 16; i++)
				M[i] = byteswap(reinterpret_cast<const T*>(data)[blk * 16 + i]);

			uint64_t totalbytes = total + (!final ? (blk + 1) * sizeof(M) * 8 : 0);
			T t0 = static_cast<T>(totalbytes);
			T t1 = sizeof(T) == 8 ? 0 : static_cast<T>(totalbytes >> 32);
			if (padding)
				t0 = t1 = 0;

			T v[16];
			memcpy(v, H.data(), sizeof(T) * 8);
			v[8 + 0] = H[8] ^ C<T>(0);
			v[8 + 1] = H[9] ^ C<T>(1);
			v[8 + 2] = H[10] ^ C<T>(2);
			v[8 + 3] = H[11] ^ C<T>(3);
			v[12] = t0 ^ C<T>(4);
			v[13] = t0 ^ C<T>(5);
			v[14] = t1 ^ C<T>(6);
			v[15] = t1 ^ C<T>(7);

			// The loop is fully unrolled for performance reasons
			round(0, M, v);
			round(1, M, v);
			round(2, M, v);
			round(3, M, v);
			round(4, M, v);
			round(5, M, v);
			round(6, M, v);
			round(7, M, v);
			round(8, M, v);
			round(9, M, v);
			round(10, M, v);
			round(11, M, v);
			round(12, M, v);
			round(13, M, v);
			if (sizeof(T) == 8)
			{
				round(14, M, v);
				round(15, M, v);
			}

			H[0] = H[0] ^ H[8] ^ v[0] ^ v[0 + 8];
			H[0 + 4] = H[0 + 4] ^ H[8] ^ v[0 + 4] ^ v[0 + 8 + 4];
			H[1] = H[1] ^ H[9] ^ v[1] ^ v[1 + 8];
			H[1 + 4] = H[1 + 4] ^ H[9] ^ v[1 + 4] ^ v[1 + 8 + 4];
			H[2] = H[2] ^ H[10] ^ v[2] ^ v[2 + 8];
			H[2 + 4] = H[2 + 4] ^ H[10] ^ v[2 + 4] ^ v[2 + 8 + 4];
			H[3] = H[3] ^ H[11] ^ v[3] ^ v[3 + 8];
			H[3 + 4] = H[3 + 4] ^ H[11] ^ v[3 + 4] ^ v[3 + 8 + 4];
		}
	}

	template<typename T>
	inline void set_salt(std::array<T, 12>& H, const unsigned char* salt, size_t saltlen)
	{
		if (saltlen)
			for (int i = 0; i < 4; i++)
				H[8 + i] = byteswap(reinterpret_cast<const T*>(salt)[i]);
		else
			H[8] = H[9] = H[10] = H[11] = 0;
	}
}

class blake_provider
{
public:
	static const bool is_xof = false;

	blake_provider(size_t hashsize)
		: hs(hashsize)
	{
		validate_hash_size(hashsize, {224, 256, 384, 512});
		zero_memory(u.H512);
	}

	~blake_provider()
	{
		clear();
	}

	inline void init()
	{
		pos = 0;
		total = 0;

		switch(hs)
		{
			case 512:
				u.H512[0] = 0x6A09E667F3BCC908ull;
				u.H512[1] = 0xBB67AE8584CAA73Bull;
				u.H512[2] = 0x3C6EF372FE94F82Bull;
				u.H512[3] = 0xA54FF53A5F1D36F1ull;
				u.H512[4] = 0x510E527FADE682D1ull;
				u.H512[5] = 0x9B05688C2B3E6C1Full;
				u.H512[6] = 0x1F83D9ABFB41BD6Bull;
				u.H512[7] = 0x5BE0CD19137E2179ull;
				break;
			case 384:
				u.H512[0] = 0xcbbb9d5dc1059ed8ull;
				u.H512[1] = 0x629a292a367cd507ull;
				u.H512[2] = 0x9159015a3070dd17ull;
				u.H512[3] = 0x152fecd8f70e5939ull;
				u.H512[4] = 0x67332667ffc00b31ull;
				u.H512[5] = 0x8eb44a8768581511ull;
				u.H512[6] = 0xdb0c2e0d64f98fa7ull;
				u.H512[7] = 0x47b5481dbefa4fa4ull;
				break;
			case 256:
				u.H256[0] = 0x6a09e667;
				u.H256[1] = 0xbb67ae85;
				u.H256[2] = 0x3c6ef372;
				u.H256[3] = 0xa54ff53a;
				u.H256[4] = 0x510e527f;
				u.H256[5] = 0x9b05688c;
				u.H256[6] = 0x1f83d9ab;
				u.H256[7] = 0x5be0cd19;
				break;
			case 224:
				u.H256[0] = 0xC1059ED8;
				u.H256[1] = 0x367CD507;
				u.H256[2] = 0x3070DD17;
				u.H256[3] = 0xF70E5939;
				u.H256[4] = 0xFFC00B31;
				u.H256[5] = 0x68581511;
				u.H256[6] = 0x64F98FA7;
				u.H256[7] = 0xBEFA4FA4;
				break;
		}
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, block_bytes(), block_bytes(), m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len, false, false); });
	}

	inline void set_salt(const unsigned char* salt, size_t salt_len)
	{
		if (salt_len && ((hs > 256 && salt_len != 32) || (hs <= 256 && salt_len != 16)))
			throw std::runtime_error("invalid salt length");

		if (hs > 256)
			blake_functions::set_salt(u.H512, salt, salt_len);
		else
			blake_functions::set_salt(u.H256, salt, salt_len);
	}

	inline void final(unsigned char* hash)
	{
		size_t messageend = hs > 256 ? 111 : 55;
		bool truncated = hs != 512 && hs != 256;
		bool padding = !pos;
		total += 8 * pos;
		m[pos] = pos == messageend && !truncated ? 0x81 : 0x80;
		if (pos++ > messageend)
		{
			if (block_bytes() != pos)
				memset(&m[pos], 0, block_bytes() - pos);
			transform(m.data(), 1, false, true);
			pos = 0;
			padding = true;
		}
		if (pos <= messageend)
		{
			memset(&m[pos], 0, messageend - pos);
			m[messageend] = truncated ? 0x00 : 0x01;
		}
		uint64_t mlen = byteswap(total);
		if (block_bytes() == 128)
			memset(&m[128 - 16], 0, sizeof(uint64_t));
		memcpy(&m[block_bytes() - 8], &mlen, sizeof(uint64_t));
		transform(m.data(), 1, padding, true);
		if (hs > 256)
		{
			for (int i = 0; i < 8; i++)
				u.H512[i] = byteswap(u.H512[i]);
			memcpy(hash, u.H512.data(), hash_size()/8);
		}
		else
		{
			for (int i = 0; i < 8; i++)
				u.H256[i] = byteswap(u.H256[i]);
			memcpy(hash, u.H256.data(), hash_size()/8);
		}
	}

	inline void clear()
	{
		zero_memory(u.H512);
		zero_memory(m);
	}

	inline size_t hash_size() const { return hs; }

private:
	inline size_t block_bytes() const { return hs > 256 ? 128 : 64; }

	inline void transform(const unsigned char* mp, size_t num_blks, bool padding, bool final)
	{
		if (hs > 256)
			blake_functions::transform(mp, num_blks, padding, u.H512, total, final);
		else
			blake_functions::transform(mp, num_blks, padding, u.H256, total, final);
	}

	union { std::array<uint64_t, 12> H512; std::array<uint32_t, 12> H256; } u;
	std::array<unsigned char, 128> m;
	size_t hs;
	size_t pos;
	uint64_t total;

};

} // namespace detail

} // namespace digestpp

#endif