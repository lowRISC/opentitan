/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_MIXIN_SHAKE_HPP
#define DIGESTPP_MIXIN_SHAKE_HPP

namespace digestpp
{

namespace mixin
{

/**
 * \brief Defines additional public functions for cSHAKE128 and cSHAKE256.
 * \sa hasher, cshake128, cshake256
 */
template<typename T>
class cshake_mixin
{
public:
	/**
	 * \brief Set NIST function name from std::string
	 *
	 * \param[in] function_name NIST function name string
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::cshake_mixin>& set_function_name(const std::string& function_name)
	{
		auto& shake = static_cast<hasher<T, mixin::cshake_mixin>&>(*this);
		shake.provider.set_function_name(function_name);
		shake.provider.init();
		return shake;
	}

	/**
	 * \brief Set NIST function name from raw buffer
	 *
	 * \param[in] function_name Pointer to NIST function name bytes
	 * \param[in] function_name_len NIST function name length (in bytes)
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::cshake_mixin>& set_function_name(const C* function_name, size_t function_name_len)
	{
		return set_function_name(std::string(reinterpret_cast<const char*>(function_name), function_name_len));
	}

	/**
	 * \brief Set customization from std::string
	 *
	 * \param[in] customization Customization string
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::cshake_mixin>& set_customization(const std::string& customization)
	{
		auto& shake = static_cast<hasher<T, mixin::cshake_mixin>&>(*this);
		shake.provider.set_customization(customization);
		shake.provider.init();
		return shake;
	}

	/**
	 * \brief Set customization from raw buffer
	 *
	 * \param[in] customization Pointer to customization bytes
	 * \param[in] customization_len Customization length (in bytes)
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::cshake_mixin>& set_customization(const C* customization, size_t customization_len)
	{
		return set_customization(std::string(reinterpret_cast<const char*>(customization), customization_len));
	}
};

} // namespace mixin

} // namespace digestpp

#endif // DIGESTPP_MIXIN_SHAKE_HPP