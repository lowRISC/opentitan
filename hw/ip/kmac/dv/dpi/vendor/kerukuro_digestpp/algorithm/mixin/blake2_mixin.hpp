/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_MIXINS_BLAKE2_HPP
#define DIGESTPP_MIXINS_BLAKE2_HPP

namespace digestpp
{

namespace mixin
{

/**
 * \brief Defines additional public functions for BLAKE2 family of algorithms.
 * \sa hasher, blake2s, blake2b, blake2sx, blake2bx, blake2sx_xof, blake2bx_xof
 */
template<typename T>
class blake2_mixin
{
public:
	/**
	 * \brief Set salt from std::string
	 *
	 * Supported salt size is 8 bytes for BLAKE2s and 16 bytes for BLAKE2b.
	 *
	 * \param[in] salt String with salt
	 * \throw std::runtime_error if salt size is not supported.
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::blake2_mixin>& set_salt(const std::string& salt)
	{
		return set_salt(salt.c_str(), salt.size());
	}

	/**
	 * \brief Set salt from raw buffer
	 *
	 * Supported salt size is 8 bytes for BLAKE2s and 16 bytes for BLAKE2b.
	 *
	 * \param[in] salt Pointer to salt bytes
	 * \param[in] salt_len Salt length (in bytes)
	 * \throw std::runtime_error if salt size is not supported.
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::blake2_mixin>& set_salt(const C* salt, size_t salt_len)
	{
		auto& blake = static_cast<hasher<T, mixin::blake2_mixin>&>(*this);
		blake.provider.set_salt(reinterpret_cast<const unsigned char*>(salt), salt_len);
		blake.provider.init();
		return blake;
	}

	/**
	 * \brief Set personalization from std::string
	 *
	 * Supported personalization size is 8 bytes for BLAKE2s and 16 bytes for BLAKE2b.
	 *
	 * \param[in] personalization String with personalization
	 * \throw std::runtime_error if personalization size is not supported.
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::blake2_mixin>& set_personalization(const std::string& personalization)
	{
		return set_personalization(personalization.c_str(), personalization.size());
	}

	/**
	 * \brief Set personalization from raw buffer
	 *
	 * Supported personalization size is 8 bytes for BLAKE2s and 16 bytes for BLAKE2b.
	 *
	 * \param[in] personalization Pointer to personalization bytes
	 * \param[in] personalization_len Personalization length (in bytes)
	 * \throw std::runtime_error if personalization size is not supported.
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::blake2_mixin>& set_personalization(const C* personalization, size_t personalization_len)
	{
		auto& blake = static_cast<hasher<T, mixin::blake2_mixin>&>(*this);
		blake.provider.set_personalization(reinterpret_cast<const unsigned char*>(personalization), personalization_len);
		blake.provider.init();
		return blake;
	}

	/**
	 * \brief Set key from std::string
	 *
	 * Maximum key size is 32 bytes for BLAKE2s and 64 bytes for BLAKE2b.
	 *
	 * \param[in] key String with key
	 * \throw std::runtime_error if key size is not supported.
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::blake2_mixin>& set_key(const std::string& key)
	{
		auto& blake = static_cast<hasher<T, mixin::blake2_mixin>&>(*this);
		blake.provider.set_key(key);
		blake.provider.init();
		return blake;
	}

	/**
	 * \brief Set key from raw buffer
	 *
	 * Maximum key size is 32 bytes for BLAKE2s and 64 bytes for BLAKE2b.
	 *
	 * \param[in] key Pointer to key bytes
	 * \param[in] key_len Key length (in bytes)
	 * \throw std::runtime_error if key size is not supported.
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::blake2_mixin>& set_key(const C* key, size_t key_len)
	{
		return set_key(std::string(reinterpret_cast<const char*>(key), key_len));
	}
};


} // namespace mixin

} // namespace digestpp

#endif