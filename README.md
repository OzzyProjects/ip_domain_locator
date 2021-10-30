# IP DOMAIN LOCATOR

**A perl script to parse network logs (tcpdump...) looking for any info for each domain name and IP (company, location etc)**

**COMING SOON : troubleshooting DNS engine to check legitimity of each DNS request.**

A perl script to use with any network log recording file, which gonna parse it and grab all domain names and IP.

Next step, the script will look for any informations about theses IP and domain names avoiding garbage datas (private IP etc...) : company name, location, root DNS,
city etc...

All these informations will be sorted (according to criterias provided by user). For exemple, the might includes location, domain names, company. About DNS traffic, 

the filter applied can be the querry type (AAAA, A, CNAME....).

The script works with a ligthweight embeded boolean logical parser as filter. It allow users to build complex filters with many boolean expression.

Logical operators accepted are : || (or), && (and), ! (not) and parenthesis, following rule of operator precedence.

<ins>Exemple of filters allowed for domain names:</ins>

`( google && .com ) || ( dns || .org )`
  
`godaddy || cloudflare || ( aws && amazon )`
  
**there is only one rule : minimum one space between each token** or the parser will fail to treat expression.

**Above one token or more, the logical expression has to be a single quoted string**

<ins>Here is a non-exhaustive list of options that might be used to make your research more accurate :</ins>

--filter|-s [expression]  : filter based on complex logical expression to target only some domain names

--fiilter-dns|-n [flag]   : flag = if enabled, extract only main domain name (the root part), otherwise, keep all
            
--querry-type|-q [flag]   : querry filter based on complex logical expression to target only custom types of DNS querries (CNAMES, AAAA, SOA...)

--max|-c [integer]        : maximum number of requests to do before quiting. 0 or negative value -> infinite loop (default)

--verbose|-v [flag]       : verbose mode enabled displays more infos about IP or domain names but works slower than default mode

--help|-h [flag]          : displays all options

**the --file|-f [file input] [file output] option is the only one required**

The file input is the file to work on and the file output is the name of CSV filename that will be created by the script to record all infos.

Example of some command lines :

`perl ip_domain_locator.pl -f dnslog output.csv -s '( cloud && .com ) || ( google && syndic )' -n -q 'AAAA || CNAME' -v`

With these options, the script will target only filter based domain names and querry types, keeping only the root part of domain names (-n) and will display infos 

such as company name, city, country, authoritative DNS, contact.

`perl ip_domain_locator.pl -f tcpdumplog output.csv -c 50`

The script here will target all domain names but will stop after 50 requests.

In verbose mode, the script creates a special record file named verboselog which hold all these infos.

But, with --quiet-verbose|-qv option, you can redirect the output to stdout, without any file created.



