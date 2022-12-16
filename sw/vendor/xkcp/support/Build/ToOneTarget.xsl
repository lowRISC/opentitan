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

<xsl:param name="nameTarget"/>

<xsl:template name="buildList">
    <xsl:param name="queued"/>
    <xsl:param name="explored" select="'|'"/>
    <xsl:variable name="first" select="substring-before(concat($queued, ' '), ' ')"/>
    <xsl:variable name="inheritedFromFirst" select="//*[@name=$first]/@inherits"/>
    <xsl:variable name="restOfQueue" select="substring-after($queued, ' ')"/>
    <xsl:choose>
        <xsl:when test="$first=''">
            <xsl:value-of select="$explored"/>
        </xsl:when>
        <xsl:when test="contains($explored, concat('|', $first, '|'))">
            <xsl:call-template name="buildList">
                <xsl:with-param name="queued" select="normalize-space($restOfQueue)"/>
                <xsl:with-param name="explored" select="$explored"/>
            </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
            <xsl:call-template name="buildList">
                <xsl:with-param name="queued" select="normalize-space(concat($restOfQueue, ' ', $inheritedFromFirst))"/>
                <xsl:with-param name="explored" select="concat($explored, $first, '|')"/>
            </xsl:call-template>
        </xsl:otherwise>
    </xsl:choose>

</xsl:template>

<xsl:template match="build">
    <xsl:variable name="listFragments">
        <xsl:call-template name="buildList">
            <xsl:with-param name="queued" select="$nameTarget"/>
        </xsl:call-template>
    </xsl:variable>
    <target name="{$nameTarget}">
        <xsl:apply-templates select="//*[contains($listFragments, concat('|',@name,'|'))]"/>
    </target>
</xsl:template>

<xsl:template match="target|fragment">
    <xsl:apply-templates select="*|text()"/>
</xsl:template>

<xsl:template name="getFilePrefix">
    <xsl:param name="fullPath"/>
    <xsl:param name="prefix"/>
    <xsl:choose>
        <xsl:when test="contains($fullPath, '/')">
            <xsl:call-template name="getFilePrefix">
                <xsl:with-param name="fullPath" select="substring-after($fullPath, '/')"/>
                <xsl:with-param name="prefix" select="concat($prefix, substring-before($fullPath, '/'), '/')"/>
            </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
            <xsl:value-of select="$prefix"/>
        </xsl:otherwise>
    </xsl:choose>
</xsl:template>

<xsl:template match="h|inc">
    <xsl:copy-of select="."/>
    <I><xsl:call-template name="getFilePrefix">
        <xsl:with-param name="fullPath" select="."/>
    </xsl:call-template></I>
</xsl:template>

<xsl:template match="*">
    <xsl:copy-of select="."/>
</xsl:template>

</xsl:stylesheet>
