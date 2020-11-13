/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_MIXINS_K12M14_HPP
#define DIGESTPP_MIXINS_K12M14_HPP

namespace digestpp
{

namespace mixin
{

/**
 * \brief Defines additional public functions for KangarooTwelve and MarsupilamiFourteen.
 * \sa hasher, k12, m14
 */
template<typename T>
class k12m14_mixin
{
public:

	/**
	 * \brief Set customization from std::string
	 *
	 * \param[in] customization Customization string
	 * \return Reference to hasher
	 */
	inline hasher<T, mixin::k12m14_mixin>& set_customization(const std::string& customization)
	{
		auto& k12m14 = static_cast<hasher<T, mixin::k12m14_mixin>&>(*this);
		k12m14.provider.set_customization(customization);
		k12m14.provider.init();
		return k12m14;
	}

	/**
	 * \brief Set customization from raw buffer
	 *
	 * \param[in] customization Pointer to customization bytes
	 * \param[in] customization_len Customization length (in bytes)
	 * \return Reference to hasher
	 */
	template<typename C, typename std::enable_if<detail::is_byte<C>::value>::type* = nullptr>
	inline hasher<T, mixin::k12m14_mixin>& set_customization(const C* customization, size_t customization_len)
	{
		return set_customization(std::string(reinterpret_cast<const char*>(customization), customization_len));
	}
};

} // namespace mixin

} // namespace digestpp

#endif // DIGESTPP_MIXINS_K12M14_HPP