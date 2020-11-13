/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_HASHER_HPP
#define DIGESTPP_HASHER_HPP

#include <string>
#include <array>
#include <algorithm>
#include <vector>
#include <iterator>
#include <sstream>
#include <cstring>
#include <iomanip>

#include "detail/traits.hpp"
#include "detail/stream_width_fixer.hpp"
#include "algorithm/mixin/null_mixin.hpp"

namespace digestpp
{

/**
 * \brief Main class template implementing the public API for hashing
 *
 * Individual hash functions are defined by typedefs.
 * See \ref digestpp namespace description for description of supported hash functions with usage examples.
 *
 * \param HashProvider A class implementing the algorithm via traditional init/update/final interface.
 * \param Mixin A class template which can be used to inject additional functions to the public API of the hasher.
 *
 * \sa digestpp
 */
template<class HashProvider, template <class> class Mixin = mixin::null_mixin>
class hasher : public Mixin<HashProvider>
{
	public:

	/**
	 * \brief Default constructor
	 *
	 * \available_if * HashProvider is a hash function with fixed output size, OR
	 * * HashProvider is a hash function with sensible default output size, OR
	 * * HashProvider is an extendable output function (XOF)
	 */
	template<typename H=HashProvider, typename std::enable_if<std::is_default_constructible<H>::value>::type* = nullptr>
	hasher()
	{
		provider.init();
	}

	/**
	 * \brief Constructor with hash size parameter
	 *
	 * Supported output sizes for each algorithm are listed in the description of corresponding typedef.
	 *
	 * \available_if * HashProvider supports multiple output sizes, AND
	 * * HashProvider is not an extendable output function (XOF)
	 *
	 * \param[in] hashsize Desired output digest size (in bits).
	 * \throw std::runtime_error if the requested output size is not supported by the algorithm.
	 */
	template<typename H=HashProvider, typename std::enable_if<!detail::is_xof<H>::value>::type* = nullptr>
	hasher(size_t hashsize) : provider(hashsize)
	{
		provider.init();
	}

	/**
	 * \brief Absorbs bytes from a C-style pointer to character buffer
	 * \param[in] data Pointer to data to absorb
	 * \param[in] len Size of data to absorb (in bytes)
	 * \return Reference to *this
	 *
	 * @par Example:\n
	 * @code // Calculate SHA-512/256 digest of a C array and output it in hex format
	 * unsigned char c[32];
	 * std::iota(c, c + sizeof(c), 0);
	 * cout << digestpp::sha512(256).absorb(c, sizeof(c)).hexdigest() << std::endl;
	 * @endcode
	 */
	template<typename T, typename std::enable_if<detail::is_byte<T>::value>::type* = nullptr>
	inline hasher& absorb(const T* data, size_t len)
	{
		provider.update(reinterpret_cast<const unsigned char*>(data), len);
		return *this;
	}

	/**
	 * \brief Absorbs bytes from std::basic_string
	 * \param[in] str String to absorb
	 * \return Reference to *this
	 */
	template<typename T,
		typename std::enable_if<detail::is_byte<T>::value && !std::is_same<T, std::string::value_type>::value>::type* = nullptr>
	inline hasher& absorb(const std::basic_string<T>& str)
	{
		if (!str.empty())
			provider.update(reinterpret_cast<const unsigned char*>(&str[0]), str.size());
		return *this;
	}

	/**
	 * \brief Absorbs bytes from std::string
	 * \param[in] str String to absorb
	 * \return Reference to *this
	 * @par Example:\n
	 * @code // Calculate BLAKE2b-256 digest from an std::string and output it in hex format
	 * std::string str = "The quick brown fox jumps over the lazy dog";
	 * std::cout << digestpp::blake2b(256).absorb(str).hexdigest() << std::endl;
	 * @endcode
	 */
	inline hasher& absorb(const std::string& str)
	{
		if (!str.empty())
			provider.update(reinterpret_cast<const unsigned char*>(&str[0]), str.size());
		return *this;
	}

	/**
	 * \brief Absorbs bytes from std::istream
	 * \param[in] istr Stream to absorb
	 * \return Reference to *this
	 * @par Example:\n
	 * @code // Calculate SHA-256 digest of a file and output it in hex format
	 * std::ifstream file("filename", std::ios_base::in|std::ios_base::binary);
	 * std::cout << digestpp::sha256().absorb(file).hexdigest() << std::endl;
	 * @endcode
	 */
	template<typename T, typename std::enable_if<detail::is_byte<T>::value>::type* = nullptr>
	inline hasher& absorb(std::basic_istream<T>& istr)
	{
		const int tmp_buffer_size = 10000;
		unsigned char buffer[tmp_buffer_size];
		size_t len = 0;
		while (istr.read(reinterpret_cast<T*>(buffer), sizeof(buffer)))
		{
			provider.update(buffer, sizeof(buffer));
			len += sizeof(buffer);
		}
		size_t gcount = istr.gcount();
		if (gcount)
		{
			provider.update(buffer, gcount);
			len += gcount;
		}
		return *this;
	}

	/**
	 * \brief Absorbs bytes from an iterator sequence
	 * \param[in] begin Begin iterator
	 * \param[in] end End iterator
	 * \return Reference to *this
	 *
	 * @par Example:\n
	 * @code // Calculate SHA-512 digest of a vector and output it in hex format
     * std::vector<unsigned char> v(100);
	 * std::iota(v.begin(), v.end(), 0);
	 * std::cout << digestpp::sha512().absorb(v.begin(), v.end()).hexdigest() << std::endl;
	 * @endcode
	 */
	template<typename IT>
	inline hasher& absorb(IT begin, IT end)
	{
		while (begin != end)
		{
			unsigned char byte = *begin++;
			provider.update(&byte, 1);
		}
		return *this;
	}

	/**
	 * \brief Squeeze bytes into user-provided preallocated buffer.
	 *
	 * After each invocation of this function the internal state of the hasher changes
	 * so that the next call will generate different (additional) output bytes.
	 * To reset the state and start new digest calculation, use \ref reset function.
	 *
	 * \available_if HashProvider is an extendable output function (XOF)
	 *
	 * \param[out] buf Buffer to squeeze data to; must be of byte type (char, unsigned char or signed char)
	 * \param[in] len Size of data to squeeze (in bytes)
	 */
	template<typename T, typename H=HashProvider,
		typename std::enable_if<detail::is_byte<T>::value && detail::is_xof<H>::value>::type* = nullptr>
	inline void squeeze(T* buf, size_t len)
	{
		provider.squeeze(reinterpret_cast<unsigned char*>(buf), len);
	}

	/**
	 * \brief Squeeze bytes into an output iterator.
	 *
	 * After each invocation of this function the internal state of the hasher changes
	 * so that the next call will generate different (additional) output bytes.
	 * To reset the state and start new digest calculation, use \ref reset function.
	 *
	 * \available_if HashProvider is an extendable output function (XOF)
	 *
	 * \param[in] len Size of data to squeeze (in bytes)
	 * \param[out] it output iterator to a byte container
	 * @par Example:\n
	 * @code // Generate long output using SHAKE-256 extendable output function using multiple calls to squeeze()
	 * std::vector<unsigned char> v;
	 * digestpp::shake256 xof;
	 * xof.absorb("The quick brown fox jumps over the lazy dog");
	 * xof.squeeze(1000, back_inserter(v));
	 * xof.squeeze(1000, back_inserter(v));
	 * xof.squeeze(1000, back_inserter(v));
	 * std::cout << "Squeezed " << v.size() << " bytes." << std::endl;
	 * @endcode
	 */
	template<typename OI, typename H=HashProvider, typename std::enable_if<detail::is_xof<H>::value>::type* = nullptr>
	inline void squeeze(size_t len, OI it)
	{
		std::vector<unsigned char> hash(len);
		provider.squeeze(&hash[0], len);
		std::copy(hash.begin(), hash.end(), it);
	}

	/**
	 * \brief Squeeze bytes and return them as a hex string.
	 *
	 * After each invocation of this function the internal state of the hasher changes
	 * so that the next call will generate different (additional) output bytes.
	 * To reset the state and start new digest calculation, use \ref reset function.
	 *
	 * \available_if HashProvider is an extendable output function (XOF)
	 *
	 * \param[in] len Size of data to squeeze (in bytes)
	 * \return Calculated digest as a hexademical string
	 * @par Example:\n
	 * @code // Generate 64-byte digest using customizable cSHAKE-256 algorithm and print it in hex format
	 * digestpp::cshake256 xof;
	 * xof.set_customization("My Customization");
	 * std::cout << xof.absorb("The quick brown fox jumps over the lazy dog").hexsqueeze(64) << std::endl;
	 * @endcode
	 */
	template<typename H=HashProvider, typename std::enable_if<detail::is_xof<H>::value>::type* = nullptr>
	inline std::string hexsqueeze(size_t len)
	{
		std::ostringstream res;
		res << std::setfill('0') << std::hex;
		squeeze(len, std::ostream_iterator<detail::stream_width_fixer<unsigned int, 2>>(res, ""));
		return res.str();
	}

	/**
	 * \brief Output binary digest into user-provided preallocated buffer.
	 *
	 * This function does not change the state of the hasher and can be called multiple times, producing the same result.
	 * To reset the state and start new digest calculation, use \ref reset function.
	 *
	 * \available_if HashProvider is a hash function (not XOF)
	 *
	 * \param[out] buf Buffer to squeeze data to; must be of byte type (char, unsigned char or signed char)
	 * \param[in] len Size of the buffer
	 * \throw std::runtime_error if the buffer size is not enough to fit the calculated digest
	 * (fixed by the algorithm or specified in the hasher constructor).
	 * @par Example:\n
	 * @code // Output binary digest to a raw C array
	 * unsigned char buf[32];
	 * digestpp::sha3(256).absorb("The quick brown fox jumps over the lazy dog").digest(buf, sizeof(buf));
	 * @endcode
	 */
	template<typename T, typename H=HashProvider,
		typename std::enable_if<detail::is_byte<T>::value && !detail::is_xof<H>::value>::type* = nullptr>
	inline void digest(T* buf, size_t len) const
	{
		if (len < provider.hash_size() / 8)
			throw std::runtime_error("Invalid buffer size");

		HashProvider copy(provider);
		copy.final(buf);
	}

	/**
	 * \brief Write binary digest into an output iterator.
	 *
	 * This function does not change the state of the hasher and can be called multiple times, producing the same result.
	 * To reset the state and start new digest calculation, use \ref reset function.
	 *
	 * \available_if HashProvider is a hash function (not XOF)
	 *
	 * \param[out] it Output iterator to a byte container.
	 * @par Example:\n
	 * @code // Output binary SHA3-256 digest to a vector
	 * vector<unsigned char> v;
	 * digestpp::sha3(256).absorb("The quick brown fox jumps over the lazy dog").digest(back_inserter(v));
	 * @endcode
	 */
	template<typename OI, typename H=HashProvider, typename std::enable_if<!detail::is_xof<H>::value>::type* = nullptr>
	inline void digest(OI it) const
	{
		HashProvider copy(provider);
		std::vector<unsigned char> hash(provider.hash_size() / 8);
		copy.final(&hash[0]);
		std::copy(hash.begin(), hash.end(), it);
	}

	/**
	 * \brief Return hex digest of absorbed data.
	 *
	 * This function does not change the state of the hasher and can be called multiple times, producing the same result.
	 * To reset the state and start new digest calculation, use \ref reset function.
	 *
	 * \available_if HashProvider is a hash function (not XOF)
	 *
	 * \return Calculated digest as a hexademical string
	 * @par Example:\n
	 * @code // Calculate BLAKE2b digest from a double quoted string and output it in hex format
	 * std::cout << digestpp::blake2b().absorb("The quick brown fox jumps over the lazy dog").hexdigest() << std::endl;
	 * @endcode
	 */
	template<typename H=HashProvider, typename std::enable_if<!detail::is_xof<H>::value>::type* = nullptr>
	inline std::string hexdigest() const
	{
		std::ostringstream res;
		res << std::setfill('0') << std::hex;
		digest(std::ostream_iterator<detail::stream_width_fixer<unsigned int, 2>>(res, ""));
		return res.str();
	}

	/**
	 * \brief Reset the hasher state to start new digest computation.
	 *
	 * \param[in] resetParameters if true, also clear optional parameters (personalization, salt, etc)
	 */
	inline void reset(bool resetParameters = false)
	{
		if (resetParameters)
			provider.clear();
		provider.init();
	}

private:
	friend Mixin<HashProvider>;
	HashProvider provider;
};


} // namespace digestpp

#endif // DIGESTPP_HASHER_HPP