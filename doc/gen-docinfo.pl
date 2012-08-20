#!/usr/bin/perl

use warnings;
use strict;

my @keys = qw(number date author comment);
my @revs;
{
    local $/ = '';

    while (<>) {
	my @values = split(/\|/);
	my %rev;
	foreach (@keys) {
	    $rev{$_} = shift @values;
	    $rev{$_} =~ s/^\s+|\s+$//g;
	}
	push @revs, \%rev;
    }
}

if (@revs) {
    print "<revhistory>\n";
    foreach my $rev (@revs) {
	print "  <revision>\n";
	print "    <revnumber>$rev->{number}</revnumber>\n";
	print "    <date>$rev->{date}</date>\n";
	print "    <authorinitials>$rev->{author}</authorinitials>\n";
	print "    <revremark>\n";
	print "    $rev->{comment}\n";
	print "    </revremark>\n";
	print "  </revision>\n";
    }
    print "</revhistory>\n";
}

