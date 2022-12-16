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

<xsl:key name="I" match="I" use="."/>
<xsl:key name="h" match="h" use="."/>
<xsl:key name="c" match="c|s" use="."/>
<xsl:key name="inc" match="inc" use="."/>

<xsl:output method="text" indent="no" encoding="UTF-8"/>

<xsl:template name="filename">
    <xsl:param name="fullPath"/>
    <xsl:choose>
        <xsl:when test="contains($fullPath, '/')">
            <xsl:call-template name="filename">
                <xsl:with-param name="fullPath" select="substring-after($fullPath, '/')"/>
            </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
            <xsl:value-of select="$fullPath"/>
        </xsl:otherwise>
    </xsl:choose>
</xsl:template>

<xsl:template name="getFileNameWithoutExtension">
    <xsl:param name="fullPath"/>
    <xsl:choose>
        <xsl:when test="contains($fullPath, '/')">
            <xsl:call-template name="getFileNameWithoutExtension">
                <xsl:with-param name="fullPath" select="substring-after($fullPath, '/')"/>
            </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
            <xsl:value-of select="substring-before($fullPath, '.')"/>
        </xsl:otherwise>
    </xsl:choose>
</xsl:template>

<xsl:template match="gcc">
    <!-- What follows is a shameless hack to avoid -march/-mtune=native on arm64/aarch64 with clang -->
    <xsl:if test=".= '-march=native' or .= '-mtune=native'">
        <xsl:text>ifneq ($(UNAME_M),aarch64)
            ifneq ($(UNAME_S),Darwin)
            ifneq ($(UNAME_M),riscv64)
            ifneq ($(UNAME_M),riscv32)
</xsl:text>
    </xsl:if>
    <xsl:text>CFLAGS := $(CFLAGS) </xsl:text>
    <xsl:value-of select="."/>
    <xsl:text>
</xsl:text>
    <xsl:if test=".= '-march=native' or .= '-mtune=native'">
        <xsl:text>endif
            endif
            endif
            endif
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="gas">
    <!-- What follows is a shameless hack to avoid -march/-mtune=native on arm64/aarch64 with clang -->
    <xsl:if test=".= '-march=native' or .= '-mtune=native'">
        <xsl:text>ifneq ($(UNAME_M),aarch64)
            ifneq ($(UNAME_S),Darwin)
            ifneq ($(UNAME_M),riscv64)
            ifneq ($(UNAME_M),riscv32)
</xsl:text>
    </xsl:if>
    <xsl:text>ASMFLAGS := $(ASMFLAGS) </xsl:text>
    <xsl:value-of select="."/>
    <xsl:text>
</xsl:text>
    <xsl:if test=".= '-march=native' or .= '-mtune=native'">
        <xsl:text>endif
            endif
            endif
            endif
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="define">
    <xsl:text>CFLAGS := $(CFLAGS) -D</xsl:text>
    <xsl:value-of select="."/>
    <xsl:if test="@as">="<xsl:value-of select="@as"/>"</xsl:if>
    <xsl:text>
</xsl:text>
</xsl:template>

<xsl:template match="I">
    <xsl:if test="generate-id()=generate-id(key('I', .)[1])">
        <xsl:text>INCLUDEFLAGS := $(INCLUDEFLAGS) -I</xsl:text>
        <xsl:value-of select="."/>
        <xsl:text>
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="h">
    <xsl:if test="generate-id()=generate-id(key('h', .)[1])">
        <xsl:text>HEADERS := $(HEADERS) </xsl:text>
        <xsl:value-of select="."/>
        <xsl:text>
</xsl:text>
        <xsl:text>SOURCES := $(SOURCES) </xsl:text>
        <xsl:value-of select="."/>
        <xsl:text>
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="inc">
    <xsl:if test="generate-id()=generate-id(key('inc', .)[1])">
        <xsl:text>INCLUDES := $(INCLUDES) </xsl:text>
        <xsl:value-of select="."/>
        <xsl:text>
</xsl:text>
        <xsl:text>SOURCES := $(SOURCES) </xsl:text>
        <xsl:value-of select="."/>
        <xsl:text>
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="c|s">
    <xsl:if test="generate-id()=generate-id(key('c', .)[1])">
        <xsl:text>
SOURCES := $(SOURCES) </xsl:text>
        <xsl:value-of select="."/>
        <xsl:text>
</xsl:text>
        <xsl:variable name="object">
            <xsl:text>$(BINDIR)/</xsl:text>
            <xsl:call-template name="getFileNameWithoutExtension">
                <xsl:with-param name="fullPath" select="."/>
            </xsl:call-template>
            <xsl:text>.o</xsl:text>
        </xsl:variable>
        <xsl:value-of select="$object"/>
        <xsl:text>: </xsl:text>
        <xsl:value-of select="."/>
        <xsl:text> $(HEADERS) $(INCLUDES)
</xsl:text>
        <xsl:choose>
            <xsl:when test="local-name(.) = 's'">
                <xsl:text>&#9;$(CC) $(INCLUDEFLAGS) $(ASMFLAGS) </xsl:text>
            </xsl:when>
            <xsl:otherwise>
                <xsl:text>&#9;$(CC) $(INCLUDEFLAGS) $(CFLAGS) </xsl:text>
            </xsl:otherwise>
        </xsl:choose>
        <xsl:value-of select="@gcc"/>
        <xsl:text> -c $&lt; -o $@
OBJECTS := $(OBJECTS) </xsl:text>
        <xsl:value-of select="$object"/>
        <xsl:text>
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="text()"/>

<xsl:template match="target">
    <xsl:variable name="final" select="concat('bin/', @name)"/>
    <xsl:variable name="pack" select="concat('bin/', translate(@name, '/', '_'), '.tar.gz')"/>
    <xsl:variable name="configfilepath" select="concat('bin/.build/', @name, '/')"/>
    <xsl:variable name="configfile" select="concat($configfilepath, 'config.h')"/>

    <xsl:text>all: </xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>
</xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>: </xsl:text>
    <xsl:value-of select="$final"/>
    <xsl:text>
</xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>.pack: </xsl:text>
    <xsl:value-of select="$pack"/>
    <xsl:text>

</xsl:text>
    <xsl:text>BINDIR = bin/.build/</xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>
$(BINDIR):
&#9;mkdir -p $(BINDIR)

MAKE ?= gmake
CC ?= gcc
AR = ar

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
    ASMFLAGS :=
endif
ifeq ($(UNAME_S),Darwin)
    ASMFLAGS := -x assembler-with-cpp -Wa,-defsym,old_gas_syntax=1 -Wa,-defsym,no_plt=1
endif
ifneq (,$(findstring mingw32,$(CC)))
    ASMFLAGS := -x assembler-with-cpp -Wa,-defsym,old_gas_syntax=1 -Wa,-defsym,no_plt=1
endif
ifneq (,$(findstring MINGW,$(UNAME_S)))
    ASMFLAGS := -x assembler-with-cpp -Wa,-defsym,no_type=1 -Wa,-defsym,no_size=1 -Wa,-defsym,no_plt=1
endif
ifneq (,$(findstring MSYS_NT,$(UNAME_S)))
    ASMFLAGS := -x assembler-with-cpp -Wa,-defsym,no_type=1 -Wa,-defsym,no_size=1 -Wa,-defsym,no_plt=1
endif
UNAME_M := $(shell uname -m)

</xsl:text>

    <xsl:if test="substring(@name, string-length(@name)-2, 3)='.so'">
        <xsl:text>CFLAGS := $(CFLAGS) -fpic
</xsl:text>
    </xsl:if>

    <xsl:text>HEADERS := $(HEADERS) </xsl:text>
    <xsl:value-of select="$configfile"/>
    <xsl:text>
</xsl:text>

    <xsl:text>SOURCES := $(SOURCES) </xsl:text>
    <xsl:value-of select="$configfile"/>
    <xsl:text>
</xsl:text>

    <xsl:text>INCLUDEFLAGS := $(INCLUDEFLAGS) -I</xsl:text>
    <xsl:value-of select="$configfilepath"/>
    <xsl:text>
</xsl:text>

    <xsl:apply-templates select="gcc|gas|define|I"/>
    <xsl:apply-templates select="h"/>
    <xsl:apply-templates select="inc"/>
    <xsl:apply-templates select="c|s"/>

    <xsl:text>
bin/</xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>: $(BINDIR) $(OBJECTS)
&#9;mkdir -p $(dir $@)
</xsl:text>

    <xsl:choose>
        <xsl:when test="substring(@name, string-length(@name)-1, 2)='.a'">
            <xsl:text>&#9;mkdir -p $@.headers
&#9;cp -f $(HEADERS) $@.headers/
&#9;$(AR) rcsv $@ $(OBJECTS)
</xsl:text>
        </xsl:when>
        <xsl:when test="substring(@name, string-length(@name)-2, 3)='.so'">
            <xsl:text>&#9;mkdir -p $@.headers
&#9;cp -f $(HEADERS) $@.headers/
&#9;$(CC) -shared -o $@ $(OBJECTS) $(CFLAGS)
</xsl:text>
        </xsl:when>
        <xsl:when test="substring(@name, string-length(@name)-5, 6)='.dylib'">
            <xsl:text>&#9;mkdir -p $@.headers
&#9;cp -f $(HEADERS) $@.headers/
&#9;$(CC) -dynamiclib -install_name @rpath/</xsl:text>
        <xsl:value-of select="@name"/>
        <xsl:text> $(CFLAGS) $(OBJECTS) -o $@
</xsl:text>
        </xsl:when>
        <xsl:otherwise>
            <xsl:text>&#9;$(CC) -o $@ $(OBJECTS) $(CFLAGS)
</xsl:text>
        </xsl:otherwise>
    </xsl:choose>

    <xsl:text>
</xsl:text>

    <xsl:value-of select="$pack"/>
    <xsl:text>: $(SOURCES)
&#9;mkdir -p bin/.pack/</xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>
&#9;rm -rf bin/.pack/</xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>/*
&#9;cp $(SOURCES) bin/.pack/</xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>/
&#9;cd bin/.pack/ ; tar -czf </xsl:text>
    <xsl:value-of select="concat('../../', $pack)"/>
    <xsl:text> </xsl:text>
    <xsl:value-of select="@name"/>
    <xsl:text>/*

</xsl:text>
</xsl:template>

</xsl:stylesheet>
