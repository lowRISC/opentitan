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
    xmlns="http://schemas.microsoft.com/developer/msbuild/2003"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    version='1.0'>

<xsl:key name="I" match="I" use="."/>
<xsl:key name="h" match="h" use="."/>
<xsl:key name="c" match="c|s" use="."/>
<xsl:key name="inc" match="inc" use="."/>

<xsl:template name="ConfigurationType">
    <xsl:param name="name"/>
    <xsl:choose>
        <xsl:when test="substring($name, string-length($name)-1, 2)='.a'">
            <ConfigurationType>StaticLibrary</ConfigurationType>
        </xsl:when>
        <xsl:when test="substring($name, string-length($name)-2, 3)='.so'">
            <ConfigurationType>DynamicLibrary</ConfigurationType>
        </xsl:when>
        <xsl:otherwise>
            <ConfigurationType>Application</ConfigurationType>
        </xsl:otherwise>
    </xsl:choose>
</xsl:template>

<xsl:template match="target">
	<xsl:variable name="name" select="translate(@name, '/', '\')"/>
<Project DefaultTargets="Build" ToolsVersion="4.0" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">
  <ItemGroup Label="ProjectConfigurations">
    <ProjectConfiguration Include="Debug|Win32">
      <Configuration>Debug</Configuration>
      <Platform>Win32</Platform>
    </ProjectConfiguration>
    <ProjectConfiguration Include="Debug|x64">
      <Configuration>Debug</Configuration>
      <Platform>x64</Platform>
    </ProjectConfiguration>
    <ProjectConfiguration Include="Debug|ARM64">
      <Configuration>Debug</Configuration>
      <Platform>ARM64</Platform>
    </ProjectConfiguration>
    <ProjectConfiguration Include="Release|Win32">
      <Configuration>Release</Configuration>
      <Platform>Win32</Platform>
    </ProjectConfiguration>
    <ProjectConfiguration Include="Release|x64">
      <Configuration>Release</Configuration>
      <Platform>x64</Platform>
    </ProjectConfiguration>
    <ProjectConfiguration Include="Release|ARM64">
      <Configuration>Release</Configuration>
      <Platform>ARM64</Platform>
    </ProjectConfiguration>
  </ItemGroup>
  <PropertyGroup Label="Globals">
    <ProjectGuid>{6F1C9407-7A01-444D-A07B-7DAE147F22A1}</ProjectGuid>
    <RootNamespace>XKCP</RootNamespace>
  </PropertyGroup>
  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.Default.props" />
  <PropertyGroup Condition="'$(RuntimeLibrary)'==''">
    <RuntimeLibrary Condition="'$(Configuration)'=='Debug'">MultiThreadedDebugDll</RuntimeLibrary>
    <RuntimeLibrary Condition="'$(Configuration)'=='Release'">MultiThreadedDll</RuntimeLibrary>
  </PropertyGroup>
  <PropertyGroup Condition="'$(Configuration)'=='Debug'" Label="Configuration">
    <xsl:call-template name="ConfigurationType"><xsl:with-param name="name" select="$name"/></xsl:call-template>
    <UseDebugLibraries>true</UseDebugLibraries>
    <PlatformToolset>v142</PlatformToolset>
    <CharacterSet>MultiByte</CharacterSet>
  </PropertyGroup>
  <PropertyGroup Condition="'$(Configuration)'=='Release'" Label="Configuration">
    <xsl:call-template name="ConfigurationType"><xsl:with-param name="name" select="$name"/></xsl:call-template>
    <UseDebugLibraries>false</UseDebugLibraries>
    <PlatformToolset>v142</PlatformToolset>
    <WholeProgramOptimization>true</WholeProgramOptimization>
    <CharacterSet>MultiByte</CharacterSet>
  </PropertyGroup>
  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.props" />
  <ImportGroup Label="ExtensionSettings">
  </ImportGroup>
  <ImportGroup Label="PropertySheets" Condition="'$(Configuration)|$(Platform)'=='Debug|Win32'">
    <Import Project="$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props" Condition="exists('$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props')" Label="LocalAppDataPlatform" />
  </ImportGroup>
  <ImportGroup Label="PropertySheets" Condition="'$(Configuration)|$(Platform)'=='Release|Win32'">
    <Import Project="$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props" Condition="exists('$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props')" Label="LocalAppDataPlatform" />
  </ImportGroup>
  <PropertyGroup Label="UserMacros" />
  <PropertyGroup Condition="'$(Configuration)'=='Debug'">
    <OutDir>$(ProjectDir)\<xsl:value-of select="$name"/>\$(Configuration)_$(Platform)\</OutDir>
    <IntDir>$(ProjectDir)\<xsl:value-of select="$name"/>\$(Configuration)_$(Platform)\</IntDir>
  </PropertyGroup>
  <PropertyGroup Condition="'$(Configuration)'=='Release'">
    <OutDir>$(ProjectDir)\<xsl:value-of select="$name"/>\$(Configuration)_$(Platform)\</OutDir>
    <IntDir>$(ProjectDir)\<xsl:value-of select="$name"/>\$(Configuration)_$(Platform)\</IntDir>
  </PropertyGroup>
  <ItemDefinitionGroup Condition="'$(Configuration)'=='Debug'">
    <ClCompile>
      <RuntimeLibrary>$(RuntimeLibrary)</RuntimeLibrary>
      <WarningLevel>Level3</WarningLevel>
      <Optimization>Disabled</Optimization>
      <AdditionalIncludeDirectories>$(ProjectDir)\<xsl:value-of select="$name"/>\config;<xsl:apply-templates select="I"/></AdditionalIncludeDirectories>
	  <PreprocessorDefinitions><xsl:apply-templates select="define"/>%(PreprocessorDefinitions)</PreprocessorDefinitions>
	  <xsl:apply-templates select="msvc"/>
    </ClCompile>
    <Link>
      <GenerateDebugInformation>true</GenerateDebugInformation>
    </Link>
  </ItemDefinitionGroup>
  <ItemDefinitionGroup Condition="'$(Configuration)'=='Release'">
    <ClCompile>
      <RuntimeLibrary>$(RuntimeLibrary)</RuntimeLibrary>
      <WarningLevel>Level3</WarningLevel>
      <Optimization>MaxSpeed</Optimization>
      <FunctionLevelLinking>true</FunctionLevelLinking>
      <IntrinsicFunctions>true</IntrinsicFunctions>
      <AdditionalIncludeDirectories>$(ProjectDir)\<xsl:value-of select="$name"/>\config;<xsl:apply-templates select="I"/></AdditionalIncludeDirectories>
	  <PreprocessorDefinitions><xsl:apply-templates select="define"/>%(PreprocessorDefinitions)</PreprocessorDefinitions>
	  <xsl:apply-templates select="msvc"/>
    </ClCompile>
    <Link>
      <GenerateDebugInformation>true</GenerateDebugInformation>
      <EnableCOMDATFolding>true</EnableCOMDATFolding>
      <OptimizeReferences>true</OptimizeReferences>
    </Link>
  </ItemDefinitionGroup>
  <ItemGroup>
    <xsl:apply-templates select="h|inc"/>
  </ItemGroup>
  <ItemGroup>
    <xsl:apply-templates select="c|s"/>
  </ItemGroup>
  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.targets" />
  <ImportGroup Label="ExtensionTargets">
  </ImportGroup>
</Project>
</xsl:template>

<xsl:template match="I">
    <xsl:if test="generate-id()=generate-id(key('I', .)[1])">
        <xsl:text>$(ProjectDir)..\..\</xsl:text>
        <xsl:value-of select="translate(., '/', '\')"/>
        <xsl:text>;</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="h">
    <xsl:if test="generate-id()=generate-id(key('h', .)[1])">
        <ClInclude Include="{concat('..\..\', translate(., '/', '\'))}"/>
        <xsl:text>
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="inc">
    <xsl:if test="generate-id()=generate-id(key('inc', .)[1])">
        <ClInclude Include="{concat('..\..\', translate(., '/', '\'))}"/>
        <xsl:text>
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="c">
    <xsl:if test="generate-id()=generate-id(key('c', .)[1])">
        <ClCompile Include="{concat('..\..\', translate(., '/', '\'))}"/>
        <xsl:text>
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="s">
    <xsl:message terminate="yes">The file '<xsl:value-of select="."/>' is a GCC assembly file and cannot be included in a Microsoft Visual Studio project.</xsl:message>
</xsl:template>

<xsl:template match="msvc">
	<AdditionalOptions><xsl:value-of select="."/></AdditionalOptions>
</xsl:template>

<xsl:template match="define">
	<xsl:value-of select="."/>
	<xsl:text>;</xsl:text>
</xsl:template>

<xsl:template match="*|text()"/>

</xsl:stylesheet>
