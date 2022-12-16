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

<xsl:output method="text" indent="no" encoding="UTF-8"/>

<xsl:template match="target">
    <xsl:variable name="targetfile" select="concat('bin/.build/', @name, '.target')"/>
    <xsl:variable name="makefile" select="concat('bin/.build/', @name, '.make')"/>
    <xsl:variable name="configfile" select="concat('bin/.build/', @name, '/config.h')"/>
    <xsl:variable name="object" select="concat('bin/', @name)"/>
    <xsl:variable name="pack" select="concat(@name, '.pack')"/>
    <xsl:variable name="vcxprojname" select="concat(@name, '.vcxproj')"/>
    <xsl:variable name="vcxprojdir" select="concat('bin/VC/', @name, '/')"/>
    <xsl:variable name="vcxprojfile" select="concat('bin/VC/', translate(@name, '/', '_'), '.vcxproj')"/>
    <xsl:variable name="all" select="../@all"/>

    <xsl:if test="$all!=''">
        <xsl:value-of select="$all"/>
        <xsl:text>: </xsl:text>
        <xsl:value-of select="@name"/>
        <xsl:text>
</xsl:text>
        <xsl:value-of select="$all"/>
        <xsl:text>.packs: </xsl:text>
        <xsl:value-of select="$pack"/>
        <xsl:text>
</xsl:text>
    </xsl:if>

    <xsl:text>.PHONY: </xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="$object"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="$pack"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="$vcxprojname"/>
    <xsl:text>
</xsl:text>

    <xsl:value-of select="@name"/>
    <xsl:text>: </xsl:text>
    <xsl:value-of select="$configfile"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="$object"/>
    <xsl:text>
</xsl:text>

    <xsl:value-of select="$object"/>
    <xsl:text>: </xsl:text>
    <xsl:value-of select="$makefile"/>
    <xsl:text>
&#9;$(MAKE) -f </xsl:text>
    <xsl:value-of select="$makefile"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>
</xsl:text>

    <xsl:value-of select="$pack"/>
    <xsl:text>: </xsl:text>
    <xsl:value-of select="$makefile"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="$configfile"/>
    <xsl:text>
&#9;$(MAKE) -f </xsl:text>
    <xsl:value-of select="$makefile"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="$pack"/>
    <xsl:text>
</xsl:text>

    <xsl:value-of select="$vcxprojname"/>
    <xsl:text>: </xsl:text>
    <xsl:value-of select="$vcxprojfile"/>
    <xsl:text>
</xsl:text>

    <xsl:value-of select="$vcxprojfile"/>
    <xsl:text>: </xsl:text>
    <xsl:value-of select="$targetfile"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="$configfile"/>
    <xsl:text>
&#9;mkdir -p </xsl:text>
	<xsl:value-of select="$vcxprojdir"/>/config<xsl:text>
&#9;cp </xsl:text>
	<xsl:value-of select="$configfile"/>
	<xsl:text> </xsl:text>
	<xsl:value-of select="$vcxprojdir"/><xsl:text>/config
&#9;xsltproc -o $@ support/Build/ToVCXProj.xsl </xsl:text>
    <xsl:value-of select="$targetfile"/>
    <xsl:text>
</xsl:text>

    <xsl:value-of select="$makefile"/>
    <xsl:text>: </xsl:text>
    <xsl:value-of select="$targetfile"/>
    <xsl:text> support/Build/ToTargetMakefile.xsl
&#9;mkdir -p $(dir $@)
&#9;xsltproc -o $@ support/Build/ToTargetMakefile.xsl $&lt;
</xsl:text>

    <xsl:value-of select="$configfile"/>
    <xsl:text>: </xsl:text>
    <xsl:value-of select="$targetfile"/>
    <xsl:text> support/Build/ToTargetConfigFile.xsl
&#9;mkdir -p $(dir $@)
&#9;xsltproc -o $@ support/Build/ToTargetConfigFile.xsl $&lt;
</xsl:text>

    <xsl:value-of select="$targetfile"/>
    <xsl:text>: support/Build/ToOneTarget.xsl bin/.build/Makefile.expanded Makefile.build
&#9;mkdir -p $(dir $@)
&#9;xsltproc -o $@ -param nameTarget "'</xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>'" support/Build/ToOneTarget.xsl bin/.build/Makefile.expanded

</xsl:text>
</xsl:template>

<xsl:template match="group">
    <xsl:if test="@all!=''">
        <xsl:text>.PHONY: </xsl:text>
        <xsl:value-of select="@all"/>
        <xsl:text> </xsl:text>
        <xsl:value-of select="@all"/><xsl:text>.packs</xsl:text>
        <xsl:text>
</xsl:text>
        <xsl:if test="../@all!=''">
            <xsl:value-of select="../@all"/>
            <xsl:text>: </xsl:text>
            <xsl:value-of select="@all"/>
            <xsl:text>
</xsl:text>
            <xsl:value-of select="../@all"/><xsl:text>.packs</xsl:text>
            <xsl:text>: </xsl:text>
            <xsl:value-of select="@all"/><xsl:text>.packs</xsl:text>
            <xsl:text>
</xsl:text>
        </xsl:if>
    </xsl:if>

    <xsl:apply-templates select="target|group"/>
</xsl:template>

<xsl:template match="group" mode="list">
    <xsl:if test="@all!=''">
        <xsl:text>&#9;@echo "+ </xsl:text>
        <xsl:value-of select="@all"/>
        <xsl:text>[.packs]"
</xsl:text>
    </xsl:if>
    <xsl:apply-templates select="target|group" mode="list"/>
</xsl:template>

<xsl:template match="target" mode="list">
    <xsl:text>&#9;@echo "- </xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>[.pack|.vcxproj]"
</xsl:text>
</xsl:template>

<xsl:template match="build">
<xsl:text>.PHONY: _list
_list:
&#9;@echo "The defined targets (-) and groups of targets (+) are:"
</xsl:text>
    <xsl:if test="@all!=''">
        <xsl:text>&#9;@echo "+ </xsl:text>
        <xsl:value-of select="@all"/>
        <xsl:text>[.packs]"
</xsl:text>
    </xsl:if>
    <xsl:apply-templates select="target|group" mode="list"/>
        <xsl:text>
</xsl:text>

    <xsl:if test="@all!=''">
        <xsl:text>.PHONY: </xsl:text>
        <xsl:value-of select="@all"/>
        <xsl:text> </xsl:text>
        <xsl:value-of select="@all"/><xsl:text>.packs</xsl:text>
        <xsl:text>
</xsl:text>
    </xsl:if>

    <xsl:apply-templates select="target|group"/>
</xsl:template>

</xsl:stylesheet>
