<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
		version='1.0'>
 <xsl:import href="http://docbook.sourceforge.net/release/xsl/current/html/docbook.xsl"/>
 <xsl:output method="html" encoding="UTF-8" indent="no" />
 <xsl:param name="generate.toc">
   appendix  nop
   article   toc,title
   book      toc,title,figure,table,example,equation
   part      nop
   preface   nop
   qandadiv  nop
   qandaset  nop
   reference toc,title
   section   nop
   set       toc
 </xsl:param>
</xsl:stylesheet>
