/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_SHA2_HPP
#define DIGESTPP_PROVIDERS_SHA2_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/sha2_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace sha2_functions
{
	template<typename T>
	static inline T Ch(T x, T y, T z)
	{
		return (x & y) ^ (~x & z);
	}

	template<typename T>
	static inline T Maj(T x, T y, T z)
	{
		return (x & y) ^ (x & z) ^ (y & z);
	}

	static inline uint64_t sum0(uint64_t x)
	{
		return rotate_right(x, 28) ^ rotate_right(x, 34) ^ rotate_right(x, 39);
	}

	static inline uint64_t sum1(uint64_t x)
	{
		return rotate_right(x, 14) ^ rotate_right(x, 18) ^ rotate_right(x, 41);
	}

	static inline uint64_t sigma0(uint64_t x)
	{
		return rotate_right(x, 1) ^ rotate_right(x, 8) ^ (x >> 7);
	}

	static inline uint64_t sigma1(uint64_t x)
	{
		return rotate_right(x, 19) ^ rotate_right(x, 61) ^ (x >> 6);
	}

	static inline uint32_t sum0(uint32_t x)
	{
		return rotate_right(x, 2) ^ rotate_right(x, 13) ^ rotate_right(x, 22);
	}

	static inline uint32_t sum1(uint32_t x)
	{
		return rotate_right(x, 6) ^ rotate_right(x, 11) ^ rotate_right(x, 25);
	}

	static inline uint32_t sigma0(uint32_t x)
	{
		return rotate_right(x, 7) ^ rotate_right(x, 18) ^ (x >> 3);
	}

	static inline uint32_t sigma1(uint32_t x)
	{
		return rotate_right(x, 17) ^ rotate_right(x, 19) ^ (x >> 10);
	}
}

// SHA-224, SHA-256, SHA-384, SHA-512/t algorithm
// SHA-512/t supports any output size up to 512 bits; in this case O must be 0 and output size provided to the constructor
template<typename T, size_t O = 0>
class sha2_provider
{
public:
	static const bool is_xof = false;

	template<typename t=T, size_t o=O, typename std::enable_if<o && (sizeof(t) == 4 || o == 384)>::type* = nullptr>
	sha2_provider()
		: hs(O)
	{
	}

	template<typename t=T, size_t o=O, typename std::enable_if<sizeof(t) == 8 && !o>::type* = nullptr>
	sha2_provider(size_t hashsize = N)
		: hs(hashsize)
	{
		detail::validate_hash_size(hashsize, N);
	}

	~sha2_provider()
	{
		clear();
	}

	inline void init()
	{
		pos = 0;
		total = 0;

		// precalculated initial values for most common output sizes
		switch(hs)
		{
			case 224:
				H[0] = 0x8C3D37C819544DA2ull;
				H[1] = 0x73E1996689DCD4D6ull;
				H[2] = 0x1DFAB7AE32FF9C82ull;
				H[3] = 0x679DD514582F9FCFull;
				H[4] = 0x0F6D2B697BD44DA8ull;
				H[5] = 0x77E36F7304C48942ull;
				H[6] = 0x3F9D85A86A1D36C8ull;
				H[7] = 0x1112E6AD91D692A1ull;
				return;
			case 256:
				H[0] = 0x22312194FC2BF72Cull;
				H[1] = 0x9F555FA3C84C64C2ull;
				H[2] = 0x2393B86B6F53B151ull;
				H[3] = 0x963877195940EABDull;
				H[4] = 0x96283EE2A88EFFE3ull;
				H[5] = 0xBE5E1E2553863992ull;
				H[6] = 0x2B0199FC2C85B8AAull;
				H[7] = 0x0EB72DDC81C52CA2ull;
				return;
			case 384:
				H[0] = 0xcbbb9d5dc1059ed8ull;
				H[1] = 0x629a292a367cd507ull;
				H[2] = 0x9159015a3070dd17ull;
				H[3] = 0x152fecd8f70e5939ull;
				H[4] = 0x67332667ffc00b31ull;
				H[5] = 0x8eb44a8768581511ull;
				H[6] = 0xdb0c2e0d64f98fa7ull;
				H[7] = 0x47b5481dbefa4fa4ull;
				return;
			default:
				H[0] = 0x6a09e667f3bcc908ull;
				H[1] = 0xbb67ae8584caa73bull;
				H[2] = 0x3c6ef372fe94f82bull;
				H[3] = 0xa54ff53a5f1d36f1ull;
				H[4] = 0x510e527fade682d1ull;
				H[5] = 0x9b05688c2b3e6c1full;
				H[6] = 0x1f83d9abfb41bd6bull;
				H[7] = 0x5be0cd19137e2179ull;
		}
		if (hs == 512)
			return;

		// calculate initial values for SHA-512/t with a different output size
		for (int i = 0; i < 8; i++)
			H[i] ^= 0xa5a5a5a5a5a5a5a5ull;
		std::string tmp = "SHA-512/" + std::to_string(hs);

		update(reinterpret_cast<unsigned char*>(&tmp[0]), tmp.length());
		unsigned char buf[512 / 8];
		final(buf);
		for (int i = 0; i < 8; i++)
			H[i] = byteswap(H[i]);
		pos = 0;
		total = 0;
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, N / 4, N / 4, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len); });
	}

	inline void final(unsigned char* hash)
	{
		total += pos * 8;
		m[pos++] = 0x80;
		if (pos > N / 4 - sizeof(T) * 2) {
			if (pos != N / 4)
				memset(&m[pos], 0, N / 4 - pos);
			transform(m.data(), 1);
			pos = 0;
		}
		memset(&m[pos], 0, N / 4 - pos);
		uint64_t mlen = byteswap(total);
		memcpy(&m[N / 4 - 8], &mlen, 64 / 8);
		transform(m.data(), 1);
		for (int i = 0; i < 8; i++)
			H[i] = byteswap(H[i]);
		memcpy(hash, &H[0], hs/8);
	}

	inline void clear()
	{
		zero_memory(H);
		zero_memory(m);
	}

	inline size_t hash_size() const { return hs; }

	inline T getK(int t) const;

private:
	inline void transform(const unsigned char* data, size_t num_blks)
	{
		for (size_t blk = 0; blk < num_blks; blk++)
		{
			T M[16];
			for (int i = 0; i < 16; i++)
				M[i] = byteswap(reinterpret_cast<const T*>(data)[blk * 16 + i]);

			const int rounds = N == 512 ? 80 : 64;
			T W[rounds];
			for (int t = 0; t <= 15; t++)
				W[t] = M[t];
			for (int t = 16; t < rounds; t++)
				W[t] = sha2_functions::sigma1(W[t - 2]) + W[t - 7] + sha2_functions::sigma0(W[t - 15]) + W[t - 16];

			T a = H[0];
			T b = H[1];
			T c = H[2];
			T d = H[3];
			T e = H[4];
			T f = H[5];
			T g = H[6];
			T h = H[7];

			for (int t = 0; t < rounds; t++)
			{
				T T1 = h + sha2_functions::sum1(e) + sha2_functions::Ch(e, f, g) + getK(t) + W[t];
				T T2 = sha2_functions::sum0(a) + sha2_functions::Maj(a, b, c);
				h = g;
				g = f;
				f = e;
				e = d + T1;
				d = c;
				c = b;
				b = a;
				a = T1 + T2;

			}
			H[0] += a;
			H[1] += b;
			H[2] += c;
			H[3] += d;
			H[4] += e;
			H[5] += f;
			H[6] += g;
			H[7] += h;
		}

	}

	constexpr static size_t N = sizeof(T) == 8 ? 512 : 256;
	std::array<T, 8> H;
	std::array<unsigned char, N / 4> m;
	size_t pos;
	uint64_t total;
	size_t hs;
};

template<>
inline uint32_t sha2_provider<uint32_t, 256>::getK(int t) const
{
	return sha256_constants<void>::K[t];
}

template<>
inline uint32_t sha2_provider<uint32_t, 224>::getK(int t) const
{
	return sha256_constants<void>::K[t];
}

template<>
inline uint64_t sha2_provider<uint64_t, 384>::getK(int t) const
{
	return sha512_constants<void>::K[t];
}

template<>
inline uint64_t sha2_provider<uint64_t, 0>::getK(int t) const
{
	return sha512_constants<void>::K[t];
}

template<>
inline void sha2_provider<uint32_t, 224>::init()
{
	pos = 0;
	total = 0;
	H[0] = 0xc1059ed8;
	H[1] = 0x367cd507;
	H[2] = 0x3070dd17;
	H[3] = 0xf70e5939;
	H[4] = 0xffc00b31;
	H[5] = 0x68581511;
	H[6] = 0x64f98fa7;
	H[7] = 0xbefa4fa4;
}

template<>
inline void sha2_provider<uint32_t, 256>::init()
{
	pos = 0;
	total = 0;
	H[0] = 0x6a09e667;
	H[1] = 0xbb67ae85;
	H[2] = 0x3c6ef372;
	H[3] = 0xa54ff53a;
	H[4] = 0x510e527f;
	H[5] = 0x9b05688c;
	H[6] = 0x1f83d9ab;
	H[7] = 0x5be0cd19;
}

} // namespace detail

} // namespace digestpp

#endif