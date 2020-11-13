/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_MIXINS_BLAKE_HPP
#define DIGESTPP_MIXINS_BLAKE_HPP

namespace digestpp
{

namespace mixin
{

/**
 * \brief Defines additional public functions for BLAKE algorithm.
 * \sa hasher, blake
 */
template<typename T>
class blake_mixin
{
public:

	/**
	 * \brief Set salt from std::string
	 *
	 * Supported salt size is 16 bytes for BLAKE-224, BLAKE-256 and 32 bytes for BLAKE-384, BLAKE-512.
	 *
	 * \param[in] salt String with salt
	 * \throw std::runtime_error if salt size is not supported.
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::blake_mixin>& set_salt(const std::string& salt)
	{
		return set_salt(salt.c_str(), salt.size());
	}

	/**
	 * \brief Set salt from raw buffer
	 *
	 * Supported salt size is 16 bytes for BLAKE-224, BLAKE-256 and 32 bytes for BLAKE-384, BLAKE-512.
	 *
	 * \param[in] salt Pointer to salt bytes
	 * \param[in] salt_len Salt length (in bytes)
	 * \throw std::runtime_error if salt size is not supported.
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::blake_mixin>& set_salt(const C* salt, size_t salt_len)
	{
		auto& blake = static_cast<hasher<T, mixin::blake_mixin>&>(*this);
		blake.provider.set_salt(reinterpret_cast<const unsigned char*>(salt), salt_len);
		blake.provider.init();
		return blake;
	}
};

} // namespace mixin

} // namespace digestpp

#endif