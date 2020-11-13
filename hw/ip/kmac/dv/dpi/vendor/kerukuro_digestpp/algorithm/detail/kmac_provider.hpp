/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_KMAC_HPP
#define DIGESTPP_PROVIDERS_KMAC_HPP

#include "shake_provider.hpp"

namespace digestpp
{

namespace detail
{

namespace kmac_functions
{
	template<size_t B>
	inline std::string bytepad(const std::string& str)
	{
		const size_t pad = B == 128 ? 168 : 136;
		unsigned char buf[32];
		size_t len = shake_functions::left_encode(pad, buf);
		std::string res(reinterpret_cast<const char*>(buf), len);
		len = shake_functions::left_encode(str.length() * 8, buf);
		res.append(reinterpret_cast<const char*>(buf), len);
		res.append(str);
		size_t delta = pad - res.size() % pad;
		if (delta && delta != pad)
			res.append(delta, '\x00');
		return res;
	}

} // namespace kmac_functions


template<size_t B, bool XOF>
class kmac_provider
{
public:
	static const bool is_xof = XOF;

	template<bool xof=XOF, typename std::enable_if<!xof>::type* = nullptr>
	kmac_provider(size_t hashsize) : hs(hashsize)
	{
		static_assert(B == 128 || B == 256, "KMAC only supports 128 and 256 bits");
		validate_hash_size(hashsize, SIZE_MAX);
		set_key("");
	}

	template<bool xof=XOF, typename std::enable_if<xof>::type* = nullptr>
	kmac_provider() : hs(0)
	{
		static_assert(B == 128 || B == 256, "KMAC only supports 128 and 256 bits");
		set_key("");
	}

	~kmac_provider()
	{
		clear();
	}

	inline void set_key(const std::string& key)
	{
		K = kmac_functions::bytepad<B>(key);
	}

	inline void set_customization(const std::string& customization)
	{
		shake.set_customization(customization);
	}

	inline void init()
	{
		squeezing = false;
		shake.set_function_name("KMAC");
		shake.init();
		update(reinterpret_cast<const unsigned char*>(K.data()), K.length());
	}

	inline void update(const unsigned char* data, size_t len)
	{
		shake.update(data, len);
	}

	inline void squeeze(unsigned char* hash, size_t hs)
	{
		if (!squeezing)
		{
			unsigned char buf[32];
			size_t len = shake_functions::right_encode(!XOF ? hs * 8 : 0, buf, false);
			update(buf, len);
			squeezing = true;
		}
		shake.squeeze(hash, hs);
	}

	inline void final(unsigned char* hash)
	{
		squeeze(hash, hs / 8);
	}

	inline void clear()
	{
		shake.clear();
		zero_memory(K);
		set_key("");
	}

	inline size_t hash_size() const
	{
		return hs;
	}

private:
	std::string K;
	size_t hs;
	bool squeezing;
	shake_provider<B, 24> shake;
};

} // namespace detail

} // namespace digestpp

#endif // DIGESTPP_PROVIDERS_KMAC_HPP