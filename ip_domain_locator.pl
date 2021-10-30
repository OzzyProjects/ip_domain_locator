#!/usr/bin/perl

##############################################################################
# File   : ip_domain_locator.pl
# Author : Etienne Armangau                     <armangau_etienne@yahoo.fr>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
# Etienne Armangau
# <armangau_etienne@yahoo.fr>
#
##############################################################################


=pod
ADDITIONNAL MODULES REQUIERED :

sudo cpan

install Carp::Assert
install Timer::Simple
install Text::CSV
    
=cut

use strict;
use warnings;
require v5.24.1;

use open qw/ :std :encoding(utf8) /;
use utf8;

use experimental 'smartmatch';

use Carp::Assert;
use Text::CSV;
use Timer::Simple;
use Getopt::Long qw(GetOptions);
use List::Util qw(any all);

# hash storing ip addresses as keys and frequences as values
my %ip_hash;

my %domain_hash;

# hash storing ip adresses as keys and domain names as values

my %resolution_table;

# array of domain names that couldn't be resolved (need to create a sub to extract only main subdomain

my @domain_error_fails;

# the state for the MT pseudorandom generator (not implemented)

my $random_state;

# Timer::Simple object
my $tick;

# seed for PRNG
my $seed;

# PID of current script
my $pid;

my @boolean_operators = ('||', '&&', '!', '(', ')');

# regex to get entire domain name with sub domains

my $domain_pattern = qr/(((?!-)[A-Za-z0–9-]{1,63}(?<!-)\.)+[A-Za-z]{2,6})/;

# regex to get only main part of domain name (need to be improved)

my $main_domain_pattern = qr/((?!-)[^.\s\-]{5,}\.[^.\s]{2,4})\./;

my $ip_pattern =
qr/((?:(?:[01]?\d{1,2}|2[0-4]\d|25[0-5])\.){3}(?:[01]?\d{1,2}|2[0-4]\d|25[0-5]))/;

my $private_ip_pattern =
qr/(127\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}$)|(^10\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}$)|(^172\.1[6-9]{1}[0-9]{0,1}\.[0-9]{1,3}\.[0-9]{1,3})|
(172\.2[0-9]{1}[0-9]{0,1}\.[0-9]{1,3}\.[0-9]{1,3})|(172\.3[0-1]{1}[0-9]{0,1}\.[0-9]{1,3}\.[0-9]{1,3})|(192\.168\.[0-9]{1,3}\.[0-9]{1,3})/;

# this scalar var will hold the reference to a subroutine will be used to grab some infos from IP. Some are basic and quiet and other
# are much more verbose but need to be called less often with random time sleep in between.

my $callback_sub = undef;

# var options from command line

my $inp_file          = undef;  # input file from tcpdump
my $record_file       = undef;  # output file : csv
my $is_only_ip        = undef;  # skip the domain name part, i want to threat IPs
my $querry_filter     = '.*';	# DNS querry filter : A, AAAA, CNAME etc...
my $counter_requests  = 0;      # max querries : 0 or neg values -> infinite loop
my $verbose_fh        = undef;  # verbose output file handle
my $is_verbose_mode   = undef;  # verbode mode
my $is_xmode          = undef;  # verbose mode+ and stealth (slow+++)
my $domain_filter     = '.*';   # boolean expression for filtering domain names
my $is_filter_domains = undef;  # domain names filtering : only main part if enabled, otherwise all
my $is_nofile_verbose = undef;  # verbose mode without file output if enabled
my $filter_dns        = undef;  # filter dns = main domain part only or all domain names
my @opt_mains;    # non optionnal options : input file, csv output file

# ******************************************* SUBROUTINES *******************************************

# ******************************************* MT PRNG (NOT IMPLEMENTED) *******************************************

sub mersenne_srand {

    use integer;
    my @state = ( shift || time || 5489 );

    # initialise with a lesser RNG
    for ( 1 .. 624 ) {
        push @state, ( 1812433253 * ( $state[ $_ - 1 ] ^ ( $state[ $_ - 1 ] >> 30 ) ) + $_);
    }

    $random_state = {
        state  => @state,
        offset => 624
    };
}

sub mersenne_twist {

    use integer;
    my ( $u, $v ) = @_;
    my $t = ( ( $u & 0x80000000 ) | ( $v & 0x7fffffff ) ) >> 1;
    my $s = ( $v & 1 ) ? 0x9908b0df : 0;
    return $t ^ $s;
}

sub mersennee_temper {

    use integer;
    my $y = shift;
    $y ^= ( $y >> 11 );
    $y ^= ( $y << 7 ) & 0x9d2c5680;
    $y ^= ( $y << 15 ) & 0xefc60000;
    $y ^= ( $y >> 18 );
    return $y;
}

sub mersenne_rand {

    use integer;
    my $scale = shift || 1.0;

    ::srand() unless defined $random_state;

    if ( $random_state->{offset} > 623 ) {

        my $state = $random_state->{state};
        for ( 0 .. 623 ) {
            $$state[$_] = ( $$state[ ( $_ + 397 ) % 624 ] ^ twist( $$state[$_], $$state[ ( $_ + 1 ) % 624 ] ) );
        }
        
        $random_state->{offset} = 0;
    }

    my $y = temper( $random_state->{state}->[ $random_state->{offset} ] );

    #$y >>= 1; #for 31 bit perl int

    $random_state->{offset}++;
    {
        no integer;
        return $y * $scale / 2**31;
    }
}

# ************************************************* BOOLEAN LOGICAL PARSER ************************************************* 

# purpose : this set of subroutines are able to parse and evaluate by true or false any logical boolean expression with a depth of 1
# it is implemented in filter expressions to allow users making relatively complex researches
# it accepts only main boolean operators : ! (not), || (or), && (and) and parenthesis
# ex of one expression : ( com && google) || yahoo.com

sub want { /\G\s+/gc; /\G\Q$_[1]\E/gc ? shift : die "'$_[1]'" }

sub boolean_eval_expr {

    my $bool_exp = shift;
    /\G\s+/gc;
    my $value =
    /\G(T|F)/gc ? $1 :
    /\G\(/gc    ? want boolean_eval_expr(0), ')' : die "Error parsing filter expression\n";
    $value = 
    /\G\s+/gc   ? $value :
    $bool_exp <= 1 && /\G\&\&/gc ? $value eq 'T' ? boolean_eval_expr(2) : (boolean_eval_expr(2), 'F') :
    $bool_exp <= 0 && /\G\|\|/gc ? $value eq 'T' ? (boolean_eval_expr (1), 'T') : boolean_eval_expr(1) :
    return $value while 1;
    
}

# subroutine which converts any subevals (subregex) in boolean results according to match or not with the string
# from ( facebook || yahoo ) && com, returns a string like ( F || T ) && T

sub get_boolean_filter_truth{

    my $regex_filter = shift;
    my $string = shift;

    $regex_filter =~ s/!\s+/!!!/g;

    my %evals;
    
    if ($regex_filter !~ qr/\s+/){
        ($string =~ qr/$regex_filter/) ? return 'T' : return 'F';
    }
    
    for (grep { !($_ ~~ @boolean_operators)} split(/\s+/, $regex_filter)){
        if ($_ =~ qr/^!!!/){
            $_ = substr($_, 3);
            $evals{$_} = ($string =~ qr/$_/) ? 'F' : 'T';
        }
        else{
            $evals{$_} = ($string =~ qr/$_/) ? 'T' : 'F';
        }
    }

    $regex_filter =~ s/!!!//g;
    $regex_filter =~ s/$_/$evals{$_}/ for (keys %evals);

    return $regex_filter;
}


# from the simplified boolean logical expression, tells if the expression matches with the target string
# return 1 if match, 0 if not.

sub tell_the_truth{

    my $regex_filter = shift;
    my $string = shift;

    my $boolean_table = &get_boolean_filter_truth($regex_filter, $string);

    for ($boolean_table){

        my $answer = boolean_eval_expr(0);
        /\G\s*\z/ or die "Complete Parse";
        ($answer eq 'T') ? return 1 : return 0;
    }
}

# when launching a system command, we need to set up first a kind of exception manager to avoid infinite breaks etc...

sub run_bash_command {

    my $command = shift;
    my $result;

	# we need to set up a kind of exceptions manager from command line to prevent against crashes or infinite freezes (ex : internet crash....)
    eval {
        local $SIG{ALRM} = sub { die "Timeout Error : please check your connection !\n" };
        alarm 10;
        $result = `$command`;
        alarm 0;
    };

    # Catch and rethrow non timout errors
    if ($@) {
        die "FATAL ERROR : System Command Error : $@ !\n";
    }

    return $result;
}

# extracting the domain names from a tcpdump output and saving theme into hash and counting their frequencies
# need to extract only the main subdomain (not implemented yet)

sub _get_domains_from_file {

    my $counter = 0;
    open my $fh, "<:encoding(UTF-8)", shift or die "$!\n";

    # parsing the input file content

    while (<$fh>) {

        chomp;

        next unless &tell_the_truth($querry_filter, $_);

        # next if the line doesn't match with valid domain
        next unless m/$filter_dns/;

        # otherwise, let's save them in hash and count occurrence for each
        #my @domains = $content =~ /$main_domain_pattern/g;
        while (/$filter_dns/g) {
            my $match = $1;
            if ( length($match) gt 10 and $match =~ /(\.com)|(\.net)|(\.fr)|(\.org)|(\.uk)|(\.ru)|(\.us)|(.\.ukr)|(\.pl)|(\.ir)/ and &tell_the_truth($domain_filter, $match )){
                $domain_hash{$match}++;
                $counter++;
            }
        }

    }

    print "\nDONE : Domains names got successfully loaded : $counter elements\n";

    close $fh;

}


# extracting the ip address from any input file and saving theme into hash and counting their frequencies
# reject all kind of wrong IP and reject private IPs too.
# arg : file input

sub _get_ip_from_file{

  	my $counter = 0;
  	open my $fh, "<:encoding(UTF-8)", shift or die "$!\n";

  	# parsing the input file content
  	while(<$fh>){

    	chomp;

    	# next if the line doesn't match with valid IP address
    	next unless m/$ip_pattern/;

    	# otherwise, let's save them in hash and count occurrence for each
   		# we don't keep private or local ips 
    	while (m/$ip_pattern/g and $_ !~ /$private_ip_pattern/){
			$ip_hash{$1}++;
			$counter++;
    	}

  	}

  	print "\nDONE : IP addresses got successfully loaded : $counter elements\n";

  	close $fh;
  
  }


# getting IPs from domain names with the dig command. If fail, we keep the domain name in list for debugging

sub _get_ip_from_domains{

  	print "\nGetting IPs now from domain names...\n";

  	foreach my $domain(keys %domain_hash){
	
    	my $command = "dig $domain +short | tail -n1 2>&1";
    	my $ip = &run_bash_command($command);
    
		chomp $ip;
	
    	# if we couldn't manage to get the IP from domain, we save it in the resolution errors list and next
      	do { push @domain_error_fails, $domain; next;} if $ip !~ /$ip_pattern/ or $ip =~ /$private_ip_pattern/;
    
    	# or we save it or increment his occurrence if it has been already met if it's not a private ip
      	# we can update now the resolution table ip address -> domain names
      	$ip_hash{$ip}++;

        $resolution_table{$ip} = $domain unless exists($resolution_table{$ip});
  	}
  
  	# we print the number of resolution errors
  	print "\nDONE : Resolving IPs from domains finished : ", ~~@domain_error_fails, "\n";
  	
	# let's launch the last chance IP address resolution for some of domain names
    &_get_îp_from_domains_host if ~~@domain_error_fails lt 0;
}

 
# emergency IP resolution for some domain names

sub _get_îp_from_domains_host{

  	print "Last chanche IP resolution just started...\n";
  	my $counter = 0;

  	foreach my $domain(@domain_error_fails){

    	my $command = "host $domain | tail -n1 2>>&1";
    	my $result = &run_bash_command($command);

		# we just check if the response is a real IP and not a private IP
	  	my $ip = $1 if $result =~ /$ip_pattern/;
	  	next if /$private_ip_pattern/ or !$ip;
      	$ip_hash{$ip}++;
      	$counter += 1;

      	# we can update now the resolution table IP->DOMAIN NAMES
        $resolution_table{$ip} = $domain unless exists($resolution_table{$ip});
    }

  print "LAST CHANCE RESOLUTION DONE : $counter more domain names have been resolved\n";
  
}
  
# xmoode, it mixes 2 or tree subroutines to get IP infos and does random break times between each call

sub _get_ip_infos_from_xmode{

  	sleep(rand(5));

  	my $ip_address = shift;
  	my $tick_t = int($tick->elapsed);
  	my $state = int(rand()) & $tick_t;
  	my $result;

  	if ($state & 0x1){
    	$result = &_get_ip_infos_geoip_lookup($ip_address);
  	}	

  	else{
    	$result = &_get_ip_infos_curl_geoip($ip_address);
  	}

  	return $result = $result || 'Not Found';
  
}


# a common method to get some basic infos with curl command

sub _get_ip_infos_curl_geoip{

  	my $ip_address = shift;
  	my $result;

  	my $command = "curl ipinfo.io/$ip_address 2>&1";
  	my $request = &run_bash_command($command);
  
	$result = $1 if $request =~ qr/country\":\s+\"(.+)\",/;
  
  	if ($verbose_fh and $result){
	  
		print $verbose_fh "\nVerbose Information :\n\n";
	
		print $verbose_fh "IP\t: $1\n" if $request =~ qr/\"ip\":\s+\"(.+)\",/;
		print $verbose_fh "HOSTNAME\t: $1\n" if $request =~ qr/\"hostname\":\s+\"(.+)\",/;
		print $verbose_fh "COUNTRY\t: $result\n";
		print $verbose_fh "CITY\t: $1\n" if $request =~ qr/\"city\":\s+\"(.+)\",/;
		print $verbose_fh "POSTAL\t: $1\n" if $request =~ qr/\"postal\":\s+\"(.+)\",/;
		print $verbose_fh "ORG\t: $1\n" if $request =~ qr/\"org\":\s+\"(.+)\",/;
		print $verbose_fh "TIMEZONE\t: $1\n\n" if $request =~ qr/\"timezone\":\s+\"(.+)\",/;
	
	}

  	return $result = $result || 'Not Found';
}


# the simpliest way to get only country from IP address (no more)

sub _get_ip_infos_geoip_lookup{

  	my $ip_address = shift;
  	my $result;

  	my $command = "geoiplookup $ip_address";
  	my $request = &run_bash_command($command);
  
  	# if the command fails at sigle request only level, we return empty an empty string
	$result = $1 if $request =~ /,\s*(.+)$/;

  	return $result = $result || 'Not Found';
}

# Displaying infos from IP addresses and write it in CSV File (locarion, type, DNS autorithy...) | DOMAIN NAME MODE (default mode)

sub print_ip_infos{

  	my %hash_res;
  	my $counter = 1;
  
  	my(@heading) = ("IP", "IP Occ", "Domain", "Domain Occ", "Country");
  	my $csv = Text::CSV->new({binary => 1, eol => $/ }) or die "Failed to create a CSV handle: $!\n";
  	open my $fh, ">:encoding(UTF-8)", $record_file or die "failed to create csv file : $!\n";
  	$csv->print($fh, \@heading);

  	foreach my $ipkey(sort { $ip_hash{$b} <=> $ip_hash{$a}} keys %ip_hash){
	  
		# checking for max number requests. if true = limit reached -> break
		if ($counter == $counter_requests){
			last;
		}

   		 # printing some basic infos about domain names and country
		print "$ipkey\t$ip_hash{$ipkey}\t$resolution_table{$ipkey}\t$domain_hash{$resolution_table{$ipkey}}";

    	# the callback routine will display infos according to verbose mode selected or not
    	# there are 4 subroutines to display infos (default : only country to verbose plus mode : location, city, compagny, type of services etc...
    	my $result = &$callback_sub($ipkey);

    	print "\nCountry : $result\n";
    
    	# we print the output in csv for each ip/domain
		my @res = ($ipkey, $ip_hash{$ipkey}, $resolution_table{$ipkey}, $domain_hash{$resolution_table{$ipkey}}, $result);
		$csv->print($fh, \@res);

    	# we add the country in hash or increment his occurrence
    	$hash_res{$result}++;
    	$counter++;

    }
  
    close $fh;
    # displaying the results for IP locations (useless = only cloudmanagment services but i can code in perl a little bit
  
    print "\n\nGLOBAL Results for countries : \n\n";
  
    print "$_\t$hash_res{$_}\n" for (sort { $hash_res{$b} <=> $hash_res{$a}} keys %hash_res);

}


# Displaying infos from IP addresses and write it in CSV File (locarion, type, DNS autorithy...) | IP ONLY MODE

sub print_ip_only_infos{

    my %hash_res;
    my $counter = 1;
  
    my(@heading) = ("IP", "IP Occ", "Country");
    my $csv = Text::CSV->new({binary => 1, eol => $/ }) or die "Failed to create a CSV handle: $!\n";
    open my $fh, ">:encoding(UTF-8)", $record_file or die "failed to create csv file : $!\n";
    $csv->print($fh, \@heading);

    foreach my $ipkey(sort { $ip_hash{$b} <=> $ip_hash{$a}} keys %ip_hash){
	  
	    # checking for max number requests. if true = limit reached -> break
	    if ($counter == $counter_requests){
		    last;
	    }

        # printing some basic infos about domain names and country
	    print "$ipkey\t$ip_hash{$ipkey}";

        # the callback routine will display infos according to verbose mode selected or not
        # there are 4 subroutines to display infos (default : only country to verbose plus mode : location, city, compagny, type of services etc...
        my $result = &$callback_sub($ipkey);

        print "\nCountry : $result\n";
    
        # we print the output in csv for each ip/domain
	    my @res = ($ipkey, $ip_hash{$ipkey}, $result);
	    $csv->print($fh, \@res);

        # we add the country in hash or increment his occurrence
        $hash_res{$result}++;
        $counter += 1;

    }
  
    close $fh;
    # displaying the results for IP locations (useless = only cloudmanagment services but i can code in perl a little bit
  
    print "\n\nGLOBAL Results for countries : \n\n";
  
    print "$_\t$hash_res{$_}\n" for (sort { $hash_res{$b} <=> $hash_res{$a}} keys %hash_res);

}
	

# ************************************************* MAIN ******************************************

# start to initialize basic variable : a tick count and a pseudo random number to get a little entropy

print "WAITING : intializing some variables...\n";

$tick = Timer::Simple->new();
$tick->start;
$seed = &mersenne_srand;
$pid = int($$);

sleep(rand(5));

assert($pid gt 0 and $seed) if DEBUG;

unless ($tick and $seed){
    die "FATAL ERROR : tick count or seed could get set up\n";
}

print "Counter succcessfully launched ! | PID : $pid\n";

# ************************************************************ PARSING COMMAND LINE ************************************************************


# display the correct recap message according to the display mode selected (default, verbose etc...)
my $displaying_mode;

# a basic configuration for parsing the command line
Getopt::Long::Configure("posix_default", "ignore_case", "prefix_pattern=(--|-)", "require_order");

# we start by parsing the command line to set up the main options

GetOptions("file|f=s{2}" => \@opt_mains,                      # input file, output file : string = input filename (utf8) and csv output filename ! [REQUIERED or abort]
			"ip-only|i" => \$is_only_ip,                      # is only ip              : flag = skip the domain name part and load ip addresses directly
			"filter|s=s" => \$domain_filter,                  # domain filter           : string = regex to apply to filter only some domains, otherwise -> all [need to create a filter parser, in progress]
            "fiilter-dns|n"  => \$is_filter_domains,  		  # filter domains          : flag = if enabled, extract only main domain (last 2-3 parts), otherwise -> all
            "querry-type|q=s" => \$querry_filter,             # querry filter           : string = regex to apply to filter only some dns querries, otherwise -> all [need to create a filter parser, in progress]
			"max|c=i" => \$counter_requests,                  # counter_requests        : integer = max request to do before quiting. 0 or negative value -> infinite loop (default)
            "verbose|v" => \$is_verbose_mode,                 # verbose mode            : flag = displays more infos about IP ! slower method
            "x-mode|x" => \$is_xmode,                         # xmode                   : flag = verbose+++ and stealth (more than verbose++ mode) ! not free or free but restricted use ! even slower
            "no-file|qv" => \$is_nofile_verbose)              # no file verbose         : flag = do not create a verbose file output (all > stdout) 
	
or die "FATAL ERROR : Error while parsing command line\n";


# before all, we need to check if a the input file and output file have been speciefied, otherwise aborting !


die "FATAL ERROR : No input file or output file was/were specified ! Aborting....\n" if !@opt_mains or $opt_mains[1] =~ /^-\w{1,}/;

# we just check first if the input file really exists, otherwise -> aborting
if (-e $opt_mains[0]){
	$inp_file = $opt_mains[0];
}
else{
	die "FATAL ERROR : input file provided doesn't exist ! Aborting....\n";
}
	
$record_file = $opt_mains[1];

# we add the csv extention to the file output if it doesn't exist	
$record_file .= ".csv" if $record_file !~ m/\.csv$/;

# if the -n flag option is enabled, keep only main part of domain names, otherwise -> keep all
$filter_dns = ($is_filter_domains ? $main_domain_pattern : $domain_pattern);

# check if the domain filter provided is a syntactically valid regex expression and/or logical expression, otherwise -> abort the script (experimental)
# we check if subevals from complex logical expression filter are all well formed regex

if (defined($domain_filter)){

    if (scalar(split(/\s+/, $domain_filter))){
	    my $is_correct_regex = eval { qr/$domain_filter/ };
	    die "FATAL ERROR : The filter $domain_filter is not a valid regex: \n$@\n" if $@;
    }
    # otherwise, if it's a complex regex, we need to eval all subregex to catch a possible invalid pattern
    else{
	    foreach my $eval(grep { !($_ ~~ @boolean_operators) } split(/\s+/, $domain_filter)){
		    $eval =~ s/\s*//;
		    my $is_correct_regex = eval { qr/$eval/ };
		    die "FATAL ERROR : The querry filter $eval is not a valid regex: \n$@\n" if $@;
	    }
    }
}


# check if the querry filter provided is a syntactically valid regex expression and/or logical expression, otherwise -> abort the script (experimental)
# we check if subevals from complex logical expression filter are all well formed regex

if (defined($querry_filter)){

    if (scalar(split(/\s+/, $querry_filter))){
	    my $is_correct_regex = eval { qr/$querry_filter/ };
	    die "FATAL ERROR : The filter $querry_filter is not a valid regex: \n$@\n" if $@;
    }
    # otherwise, if it's a complex regex, we need to eval all subregex to catch a possible invalid pattern
    else{
	    foreach my $eval(grep { !($_ ~~ @boolean_operators) } split(/\s+/, $querry_filter)){
		    $eval =~ s/\s*//;
		    my $is_correct_regex = eval { qr/$eval/ };
		    die "FATAL ERROR : The querry filter $eval is not a valid regex: \n$@\n" if $@;
	    }
    }
}

# parsing the display mode selected (quiet, verbose, verbose+ or xmode)

# if the X mode is enabled, we just need to check if a valid token has been provided, set up the callback rootine to the good subroutine
# and open the file handle for the verbose mode

if (defined($is_xmode)){
	
    $callback_sub = \&get_ip_infos_from_xmode;
    
    # if the quiet verbose file option is enabled, -qv option, we redirect the filehandle to stdout and don't create any file output
    $is_nofile_verbose ? $verbose_fh = \*STDOUT : open $verbose_fh, ">", "verboselog" or die "$!\n";
    $displaying_mode = "Script launched in X mode\n";
}

# if the verbose mode is enabled, we just need to assign the callback routine to the good sub and open the file handle for the verbose mode

elsif (defined($is_verbose_mode)){

    $callback_sub = \&_get_ip_infos_curl_geoip;
  
    # if the quiet verbose file option is enabled, option -qv, we redirect the filehandle to stdout and don't create any file output
    $is_nofile_verbose ? $verbose_fh = \*STDOUT : open $verbose_fh, ">", "verboselog" or die "$!\n";
    $displaying_mode = "Script launched in verbose mode\n";
}

# default display mode : most simple and fastest mode among others, it displays only IP countries and nothing else

else{
	
    $callback_sub = \&_get_ip_infos_geoip_lookup;
    $displaying_mode = "Script launched in normal mode (quiet mode)\n";
  
}

# ************************************************************ MAIN PART STEP ************************************************************

# recap of options selected for the research

print "\nRECAP OF OPTIONS SELECTED : \n";
print "\nStarting the domain names parsing from : $inp_file\n";
print "The CSV file output has been set up to : $record_file\n";
$is_only_ip ? print "IP only based extract infos mode\n" : print "Domain names/IP based extract infos mode (default)\n";
print "DNS querry filter provided : ";
$querry_filter eq ".*" ? print "no filter (default)\n" : print "\'$querry_filter\' (custom)\n";
print "Max requests to threat before exiting : ";
$counter_requests lt 1 ? print "(infinite loop)\n" : print "$counter_requests\n";
print "Domain names filter extractor selected : ";
$is_filter_domains ? print "main domain part\n" : print "all domain name part\n";
print "Domain names additional filter provided : ";
$domain_filter eq ".*" ? print "no filter (default)\n" : print "\'$domain_filter\' (custom)\n";
print "$displaying_mode";

if (defined($is_only_ip)){

	&_get_ip_from_file($inp_file);
	&print_ip_only_infos;
}

else{

	&_get_domains_from_file($inp_file);
	&_get_ip_from_domains;
	&print_ip_infos;
}

print "Domain names parsing successfully achieved\n";

$tick->stop;
print "INFO Total duration time : ", $tick->elapsed, "seconds \n";

# we close the verbose file output handle if opened
close $verbose_fh if defined($verbose_fh);

exit(0);


