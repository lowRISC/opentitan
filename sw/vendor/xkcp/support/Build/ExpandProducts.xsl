<?xml version='1.0' encoding="UTF-8"?>
<!--
The eXtended Keccak Code Package (XKCP)
https://github.com/XKCP/XKCP

Implementation by Gilles Van Assche, hereby denoted as "the implementer".

For more information, feedback or questions, please refer to the Keccak Team website:
https://keccak.team/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
-->
<xsl:stylesheet
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    version='1.0'>

<xsl:template name="expand">
    <xsl:param name="first"/>
    <xsl:param name="second"/>
    <xsl:param name="first-explored" select="''"/>
    <xsl:param name="second-explored" select="''"/>
    <xsl:param name="delimiter"/>
    <xsl:variable name="first-cur" select="substring-before(concat($first, ' '), ' ')"/>
    <xsl:variable name="first-rest" select="substring-after($first, ' ')"/>
    <xsl:variable name="second-cur" select="substring-before(concat($second, ' '), ' ')"/>
    <xsl:variable name="second-rest" select="substring-after($second, ' ')"/>

    <xsl:if test="($first-cur!='') and ($second-cur!='')">
        <target>
            <xsl:attribute name="name"><xsl:value-of select="concat($first-cur, $delimiter, $second-cur)"/></xsl:attribute>
            <xsl:attribute name="inherits"><xsl:value-of select="concat($first-cur, ' ', $second-cur)"/></xsl:attribute>
        </target>

        <xsl:choose>
            <xsl:when test="normalize-space($second-rest)!=''">
                <xsl:call-template name="expand">
                    <xsl:with-param name="first" select="$first"/>
                    <xsl:with-param name="first-explored" select="$first-explored"/>
                    <xsl:with-param name="second" select="$second-rest"/>
                    <xsl:with-param name="second-explored" select="normalize-space(concat($second-explored, ' ', $second-cur))"/>
                    <xsl:with-param name="delimiter" select="$delimiter"/>
                </xsl:call-template>
            </xsl:when>
            <xsl:when test="normalize-space($first-rest)!=''">
                <xsl:call-template name="expand">
                    <xsl:with-param name="first" select="$first-rest"/>
                    <xsl:with-param name="first-explored" select="normalize-space(concat($first-explored, ' ', $first-cur))"/>
                    <xsl:with-param name="second" select="normalize-space(concat($second-explored, ' ', $second-cur))"/>
                    <xsl:with-param name="second-explored" select="''"/>
                    <xsl:with-param name="delimiter" select="$delimiter"/>
                </xsl:call-template>
            </xsl:when>
        </xsl:choose>
    </xsl:if>
</xsl:template>

<xsl:template match="product">
    <xsl:call-template name="expand">
        <xsl:with-param name="first" select="normalize-space(factor[1]/@set)"/>
        <xsl:with-param name="second" select="normalize-space(factor[2]/@set)"/>
        <xsl:with-param name="delimiter">
            <xsl:choose>
                <xsl:when test="@delimiter!=''"><xsl:value-of select="@delimiter"/></xsl:when>
                <xsl:otherwise>+</xsl:otherwise>
            </xsl:choose>
        </xsl:with-param>
    </xsl:call-template>
</xsl:template>

<xsl:template match="*">
    <xsl:copy>
        <xsl:copy-of select="@*"/>
        <xsl:apply-templates/>
    </xsl:copy>
</xsl:template>

</xsl:stylesheet>
