/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_MIXINS_SKEIN_HPP
#define DIGESTPP_MIXINS_SKEIN_HPP

namespace digestpp
{

namespace mixin
{

/**
 * \brief Defines additional public functions for Skein family of algorithms.
 * \sa hasher, skein256, skein512, skein1024, skein256_xof, skein512_xof, skein1024_xof
 */
template<typename T>
class skein_mixin
{
public:
	/**
	 * \brief Set personalization from std::string
	 *
	 * \param[in] personalization Personalization string
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::skein_mixin>& set_personalization(const std::string& personalization)
	{
		auto& skein = static_cast<hasher<T, mixin::skein_mixin>&>(*this);
		skein.provider.set_personalization(personalization);
		skein.provider.init();
		return skein;
	}

	/**
	 * \brief Set personalization from raw buffer
	 *
	 * \param[in] personalization Pointer to personalization bytes
	 * \param[in] personalization_len Personalization length (in bytes)
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::skein_mixin>& set_personalization(const C* personalization, size_t personalization_len)
	{
		return set_personalization(std::string(reinterpret_cast<const char*>(personalization), personalization_len));
	}

	/**
	 * \brief Set key from std::string
	 *
	 * \param[in] key Key string
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::skein_mixin>& set_key(const std::string& key)
	{
		auto& skein = static_cast<hasher<T, mixin::skein_mixin>&>(*this);
		skein.provider.set_key(key);
		skein.provider.init();
		return skein;
	}

	/**
	 * \brief Set key from raw buffer
	 *
	 * \param[in] key Pointer to key bytes
	 * \param[in] key_len Key length (in bytes)
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::skein_mixin>& set_key(const C* key, size_t key_len)
	{
		return set_key(std::string(reinterpret_cast<const char*>(key), key_len));
	}

	/**
	 * \brief Set nonce from std::string
	 *
	 * \param[in] nonce Nonce string
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::skein_mixin>& set_nonce(const std::string& nonce)
	{
		auto& skein = static_cast<hasher<T, mixin::skein_mixin>&>(*this);
		skein.provider.set_nonce(nonce);
		skein.provider.init();
		return skein;
	}

	/**
	 * \brief Set nonce from raw buffer
	 *
	 * \param[in] nonce Pointer to nonce bytes
	 * \param[in] nonce_len Nonce length (in bytes)
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::skein_mixin>& set_nonce(const C* nonce, size_t nonce_len)
	{
		return set_nonce(std::string(reinterpret_cast<const char*>(nonce), nonce_len));
	}
};

} // namespace mixin

} // namespace digestpp

#endif