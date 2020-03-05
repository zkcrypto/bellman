<?xml version='1.0' encoding="UTF-8"?>
<!--
Implementation by Gilles Van Assche, hereby denoted as "the implementer".

For more information, feedback or questions, please refer to our website:
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
<xsl:key name="c" match="c" use="."/>

<xsl:template match="target">
<Project DefaultTargets="Build" ToolsVersion="4.0" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">
  <ItemGroup Label="ProjectConfigurations">
    <ProjectConfiguration Include="Debug|Win32">
      <Configuration>Debug</Configuration>
      <Platform>Win32</Platform>
    </ProjectConfiguration>
    <ProjectConfiguration Include="Release|Win32">
      <Configuration>Release</Configuration>
      <Platform>Win32</Platform>
    </ProjectConfiguration>
  </ItemGroup>
  <PropertyGroup Label="Globals">
    <ProjectGuid>{6F1C9407-7A01-444D-A07B-7DAE147F22A1}</ProjectGuid>
    <RootNamespace>XKCP</RootNamespace>
  </PropertyGroup>
  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.Default.props" />
  <PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Debug|Win32'" Label="Configuration">
    <ConfigurationType>Application</ConfigurationType>
    <UseDebugLibraries>true</UseDebugLibraries>
    <PlatformToolset>v110</PlatformToolset>
    <CharacterSet>MultiByte</CharacterSet>
  </PropertyGroup>
  <PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Release|Win32'" Label="Configuration">
    <ConfigurationType>Application</ConfigurationType>
    <UseDebugLibraries>false</UseDebugLibraries>
    <PlatformToolset>v110</PlatformToolset>
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
  <PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Debug|Win32'">
    <OutDir>$(SolutionDir)$(ProjectName)\$(Configuration)\</OutDir>
    <IntDir>$(SolutionDir)$(ProjectName)\$(Configuration)\</IntDir>
  </PropertyGroup>
  <PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Release|Win32'">
    <OutDir>$(SolutionDir)$(ProjectName)\$(Configuration)\</OutDir>
    <IntDir>$(SolutionDir)$(ProjectName)\$(Configuration)\</IntDir>
  </PropertyGroup>
  <ItemDefinitionGroup Condition="'$(Configuration)|$(Platform)'=='Debug|Win32'">
    <ClCompile>
      <WarningLevel>Level3</WarningLevel>
      <Optimization>Disabled</Optimization>
      <AdditionalIncludeDirectories><xsl:apply-templates select="I"/></AdditionalIncludeDirectories>
    </ClCompile>
    <Link>
      <GenerateDebugInformation>true</GenerateDebugInformation>
    </Link>
  </ItemDefinitionGroup>
  <ItemDefinitionGroup Condition="'$(Configuration)|$(Platform)'=='Release|Win32'">
    <ClCompile>
      <WarningLevel>Level3</WarningLevel>
      <Optimization>MaxSpeed</Optimization>
      <FunctionLevelLinking>true</FunctionLevelLinking>
      <IntrinsicFunctions>true</IntrinsicFunctions>
      <AdditionalIncludeDirectories><xsl:apply-templates select="I"/></AdditionalIncludeDirectories>
    </ClCompile>
    <Link>
      <GenerateDebugInformation>true</GenerateDebugInformation>
      <EnableCOMDATFolding>true</EnableCOMDATFolding>
      <OptimizeReferences>true</OptimizeReferences>
    </Link>
  </ItemDefinitionGroup>
  <ItemGroup>
    <xsl:apply-templates select="h"/>
  </ItemGroup>
  <ItemGroup>
    <xsl:apply-templates select="c"/>
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

<xsl:template match="c">
    <xsl:if test="generate-id()=generate-id(key('c', .)[1])">
        <ClCompile Include="{concat('..\..\', translate(., '/', '\'))}"/>
        <xsl:text>
</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="*|text()"/>

</xsl:stylesheet>
