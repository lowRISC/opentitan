/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_MIXINS_KMAC_HPP
#define DIGESTPP_MIXINS_KMAC_HPP

namespace digestpp
{

namespace mixin
{

/**
 * \brief Defines additional public functions for KMAC family of algorithms.
 * \sa hasher, kmac128, kmac256, kmac128_xof, kmac256_xof
 */
template<typename T>
class kmac_mixin
{
public:
	/**
	 * \brief Set key from std::string
	 *
	 * \param[in] key Key string
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::kmac_mixin>& set_key(const std::string& key)
	{
		auto& kmac = static_cast<hasher<T, mixin::kmac_mixin>&>(*this);
		kmac.provider.set_key(key);
		kmac.provider.init();
		return kmac;
	}

	/**
	 * \brief Set key from raw buffer
	 *
	 * \param[in] key Pointer to key bytes
	 * \param[in] key_len Key length (in bytes)
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::kmac_mixin>& set_key(const C* key, size_t key_len)
	{
		return set_key(std::string(reinterpret_cast<const char*>(key), key_len));
	}

	/**
	 * \brief Set customization from std::string
	 *
	 * \param[in] customization Customization string
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::kmac_mixin>& set_customization(const std::string& customization)
	{
		auto& kmac = static_cast<hasher<T, mixin::kmac_mixin>&>(*this);
		kmac.provider.set_customization(customization);
		kmac.provider.init();
		return kmac;
	}

	/**
	 * \brief Set customization from raw buffer
	 *
	 * \param[in] customization Pointer to customization bytes
	 * \param[in] customization_len Customization length (in bytes)
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::kmac_mixin>& set_customization(const C* customization, size_t customization_len)
	{
		return set_customization(std::string(reinterpret_cast<const char*>(customization), customization_len));
	}
};

} // namespace mixin

} // namespace digestpp

#endif // DIGESTPP_MIXINS_KMAC_HPP