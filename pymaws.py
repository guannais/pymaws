#/usr/bin/python3

import argparse
import base64
import boto.sts
import boto3
import calendar
import configparser
import errno
import fnmatch
import getpass
import json
import logging
import os
import pyjq
import re
import requests
import subprocess
import sys
import time
import xml.etree.ElementTree as ET
from bs4 import BeautifulSoup
from colorama import Fore, Back, Style
from datetime import datetime
from os.path import expanduser
from tabulate import tabulate
from urllib.parse import urlparse, urlunparse

####################################################
# Parse arguments from command line

parser = argparse.ArgumentParser(description='Ask for user specific information')

parser.add_argument('-c', '--configfile',
                    action="store", dest="awsconfigfile",
                    help="default AWS configfile, default is /.aws/credentials", default="/.aws/credentials")

parser.add_argument('-r', '--region',
                    action="store", dest="region",
                    help="default AWS region, default is eu-west-1", default="eu-west-1")

args = parser.parse_args()

##########################################################################
# Vars
##########################################################################

ALIAS_ROLES_DIC = {
    'arn:aws:iam::000000000001:role/ROLENAME01' : 'ROLEALIAS01',
    'arn:aws:iam::000000000002:role/ROLENAME02' : 'ROLEALIAS02',
    'arn:aws:iam::000000000003:role/ROLENAME03' : 'ROLEALIAS03',
    'arn:aws:iam::000000000004:role/ROLENAME04' : 'ROLEALIAS04'
}

REGIONS_ROLES_DIC = {
    'ROLEALIAS01' : 'us-west-1',
    'ROLEALIAS04' : 'us-west-1'
}

REGION_PREDEFINED = args.region
URL_DOMAIN = '****************'
LOGIN_DOMAIN = 'DOMAIN'
IDENTRYURL = 'https://'+URL_DOMAIN+'/adfs/ls/IdpInitiatedSignOn.aspx?loginToRp=urn:amazon:webservices'
CONFIG_FILENAME = expanduser("~") + args.awsconfigfile
HOME_DIR = os.path.expanduser("~")
DASHES = '----------------------------------------------------------------------------------------------------------------------------------------------------------'
BACKFROMINSTANCES = 0

##########################################################################
# Vars
##########################################################################

def check_file_expiration_dates():
	global PROFILE_EXPIRED

	PROFILE_EXPIRED = 0

	config = configparser.ConfigParser()
	config.read(CONFIG_FILENAME)
	alias_list = config.sections()

	if config.has_section('default'):
		alias_list.remove('default')

	alias_total = len(alias_list)

	if alias_total == 0:
		PROFILE_EXPIRED = 1
	else:
		now = datetime.utcnow()
		i = 0
		while (i < alias_total) and (PROFILE_EXPIRED == 0):
			exp = config.get(alias_list[i], 'expiration')
			expiration_date = datetime.strptime(exp, '%Y-%m-%dT%H:%M:%SZ')
			if expiration_date < now:
				PROFILE_EXPIRED = 1
			i += 1

def username_password_login():
	global session
	global response
	global username

    # Get the federated credentials from the user
	username = input('Username: '+LOGIN_DOMAIN+'\\')
	username = LOGIN_DOMAIN+'\\' + username
	password = getpass.getpass()

	# Initiate session handler
	session = requests.Session()

	# Programmatically get the SAML assertion
	# Opens the initial IdP url and follows all of the HTTP302 redirects, and
	# gets the resulting login page
	formresponse = session.get(IDENTRYURL, verify=True, timeout=10)
	# Capture the idpauthformsubmiturl, which is the final url after all the 302s
	idpauthformsubmiturl = formresponse.url

	# Parse the response and extract all the necessary values
	# in order to build a dictionary of all of the form values the IdP expects
	formsoup = BeautifulSoup(formresponse.text, "html.parser")
	payload = {}

	for inputtag in formsoup.find_all(re.compile('(INPUT|input)')):
		name = inputtag.get('name', '')
		value = inputtag.get('value', '')
		if "user" in name.lower():
			#Make an educated guess that this is the right field for the username
			payload[name] = username
		elif "email" in name.lower():
			#Some IdPs also label the username field as 'email'
			payload[name] = username
		elif "pass" in name.lower():
			#Make an educated guess that this is the right field for the password
			payload[name] = password
		else:
			#Simply populate the parameter with the existing value
			#(picks up hidden fields in the login form)
			payload[name] = value

	for inputtag in formsoup.find_all(re.compile('(FORM|form)')):
		action = inputtag.get('action')
		actionURL = urlparse(action)
		if (actionURL.scheme == '' and actionURL.netloc == '') and actionURL.path:
			parsedurl = urlparse(IDENTRYURL)
			idpauthformsubmiturl = parsedurl.scheme + "://" + parsedurl.netloc + action
		else:
			idpauthformsubmiturl = action
	# Performs the submission of the IdP login form with the above post data
	response = session.post(idpauthformsubmiturl, data=payload, verify=True)

	# Overwrite and delete the credential variables, just for safety
	username = '##############################################'
	password = '##############################################'
	del username
	del password

	if 'errorText' in response.text:
		print('Error login or password incorrect.')
		sys.exit(0)

def check_if_mfa():
	global response

	if 'pin' not in response.text:
		print('No MFA login enable for user.')
		sys.exit(0)

def mfa_login():
	global session
	global response

	# Multi-Factor Authentication (MFA) Handle
	# Depending upon the MFA provider, you may replace
	# the string found in response.text to identify the MFA
	idpauthformsubmiturl = response.url
	otp = input('OTP: ')
	formsoup = BeautifulSoup(response.text, "html.parser")
	payload = {}
	for inputtag in formsoup.find_all(re.compile('(INPUT|input)')):
		name = inputtag.get('name', '')
		value = inputtag.get('value', '')
		if "pin" in name.lower():
			# OTP
			payload[name] = otp
		else:
			if "options" not in name.lower():
				# Disable options
				payload[name] = value
	# Performs the submission of the IdP login form with the above post data
	response = session.post(idpauthformsubmiturl, data=payload, verify=True)

def check_saml_mfa():
	global assertion

	# Decode the response and extract the SAML assertion
	soup = BeautifulSoup(response.text, "html.parser")

	assertion = ''

	# Look for the SAMLResponse attribute of the input tag (determined by
	# analyzing the debug print lines above)
	for inputtag in soup.find_all('input'):
		if inputtag.get('name') == 'SAMLResponse':
			#print(inputtag.get('value'))
			assertion = inputtag.get('value')

	# Better error handling is required for production use.
	if assertion == '':
		print('Response did not contain a valid SAML assertion. MFA must be wrong.')
		sys.exit(0)

def retrive_roles():
	global assertion
	global roles_ordered
	global awsroles

	# Parse the returned assertion and extract the authorized roles
	awsroles = []
	root = ET.fromstring(base64.b64decode(assertion))

	saml_urn_attribute_value = '{urn:oasis:names:tc:SAML:2.0:assertion}AttributeValue'
	for saml2attribute in root.iter('{urn:oasis:names:tc:SAML:2.0:assertion}Attribute'):
		if saml2attribute.get('Name') == 'https://aws.amazon.com/SAML/Attributes/Role':
			for saml2attributevalue in saml2attribute.iter(saml_urn_attribute_value):
				awsroles.append(saml2attributevalue.text)

	# Note the format of the attribute value should be role_arn,principal_arn
	# but lots of blogs list it as principal_arn,role_arn so let's reverse
	# them if needed
	for awsrole in awsroles:
		chunks = awsrole.split(',')
		if'saml-provider' in chunks[0]:
			newawsrole = chunks[1] + ',' + chunks[0]
			index = awsroles.index(awsrole)
			awsroles.insert(index, newawsrole)
			awsroles.remove(awsrole)

def order_roles():
	global awsroles
	global roles_ordered
	global REGION_PREDEFINED

	# If I have more than one role, ask the user which one they want,
	# otherwise just proceed
	roles_list = []
	roles_ordered = []

	#print "please choose the role you would like to assume:"
	i = 1
	for awsrole in awsroles:
		finded = 0
		role_arn = awsrole.split(',')[0]
		role_urn = awsrole.split(',')[1]
		for ALIAS_ROLES_DIC_key, ALIAS_ROLES_DIC_value in ALIAS_ROLES_DIC.items():
			if role_arn == ALIAS_ROLES_DIC_key:
				role_region = REGION_PREDEFINED
				for REGIONS_ROLES_DIC_key, REGIONS_ROLES_DIC_value in REGIONS_ROLES_DIC.items():
					if ALIAS_ROLES_DIC_value == REGIONS_ROLES_DIC_key:
						role_region = REGIONS_ROLES_DIC_value
				roles_list.append((ALIAS_ROLES_DIC_value, role_arn, role_urn, role_region))
				finded = 1
		if finded == 0:
			roles_list.append(("NO_NAME_" + str(i), role_arn, role_urn, role_region))
			i += 1

	roles_ordered = sorted(roles_list, key=lambda x: x[0])

def write_config_file():
	global roles_ordered

	# Read in the existing config file
	config = configparser.RawConfigParser()
	config.read(CONFIG_FILENAME)
	if not config.has_section('default'):
		config.add_section('default')
		config.set('default', 'output', '')
		config.set('default', 'region', '')
		config.set('default', 'aws_access_key_id', '')
		config.set('default', 'aws_secret_access_key', '')
		config.set('default', 'aws_session_token', '')
		config.set('default', 'expiration', '')
		# Write the updated config file
		with open(CONFIG_FILENAME, 'w+') as configfile:
			config.write(configfile)

	i = 0
	for awsrole in roles_ordered:
		role_alias = roles_ordered[int(i)][0]
		role_access_key = roles_ordered[int(i)][1]
		role_secret_key = roles_ordered[int(i)][2]
		region = roles_ordered[int(i)][3]
		# Use the assertion to get an AWS STS token using Assume Role with SAML
		conn = boto.sts.connect_to_region(region)
		token = conn.assume_role_with_saml(role_access_key, role_secret_key, assertion)
		# Write the AWS STS token into the AWS credential file

		# Read in the existing config file
		config = configparser.RawConfigParser()
		config.read(CONFIG_FILENAME)

		# Put the credentials into a specific profile instead of clobbering
		# the default credentials
		if not config.has_section(role_alias):
			config.add_section(role_alias)

		config.set(role_alias, 'output', 'json')
		config.set(role_alias, 'region', region)
		config.set(role_alias, 'aws_access_key_id', token.credentials.access_key)
		config.set(role_alias, 'aws_secret_access_key', token.credentials.secret_key)
		config.set(role_alias, 'aws_session_token', token.credentials.session_token)
		config.set(role_alias, 'expiration', format(token.credentials.expiration))

		# Write the updated config file
		with open(CONFIG_FILENAME, 'w+') as configfile:
			config.write(configfile)
		i += 1

	config.remove_section('default')
	with open(CONFIG_FILENAME, 'w+') as configfile:
		config.write(configfile)

def connect_ec2():
	global client, json_data

	session = boto3.Session(profile_name=PROFILE_SELECTED)
	client = session.client('ec2')
	value = client.describe_instances()
	json_data = json.loads(json.dumps(value, default=datetimeconverter))

def datetimeconverter(json_parameter):
	if isinstance(json_parameter, datetime):
		return json_parameter.__str__()

def getKeyValuePropertyEC2Instance(INSTANCE_SELECTED, ARRAY_SEARCHED, KEY_SEARCHED, KEY_VALUE_SEARCHED, VALUE_SEARCHED):
	query = '.Reservations[].Instances[] | select(.InstanceId==\"'+INSTANCE_SELECTED+'\")'
	query = query+' | .'+ARRAY_SEARCHED+'[]'
	query = query+' | select(.'+KEY_SEARCHED+'==\"'+KEY_VALUE_SEARCHED+'\") | .'+VALUE_SEARCHED
	list = pyjq.all(query, json_data)
	if list[0] is None:
		return '-'
	else:
		return list[0]

def FindPemFile(PEM_2_SEARCH):
	global PEM_PATH

	for dName, sdName, fList in os.walk(HOME_DIR):
		for CONFIG_FILENAME in fList:
			if fnmatch.fnmatch(CONFIG_FILENAME, PEM_2_SEARCH):
				PEM_PATH = os.path.join(dName, CONFIG_FILENAME)
				break

def printManageProfilesActionMENUFooter():
	print(DASHES)
	OPTION = 'Choose profile | '+Fore.GREEN+'r'+Fore.RESET+'efresh | '
	OPTION = OPTION +Style.BRIGHT+'b'+Style.RESET_ALL+'ack | '+Fore.RED+'q'+Fore.RESET+'uit: '
	print(OPTION)

def printProfilesMENUHeader():
	global alias_list

	os.system('clear')
	print(DASHES)
	print(Style.BRIGHT+'AWS PROFILES MENU : '+Fore.RED+'EC2 Mode'+Style.RESET_ALL)
	print(DASHES)

	config = configparser.ConfigParser()
	config.read(CONFIG_FILENAME)
	alias_list = config.sections()
	for i in range(len(alias_list)):
		print('   '+str(i+1)+'. '+alias_list[i])

def printProfilesMENUFooter():
	print(DASHES)
	print('Choose profile | '+Fore.GREEN+'r'+Fore.RESET+'efresh | '+Fore.RED+'q'+Fore.RESET+'uit: ')

def EC2InstancesMenu():
	global INSTANCE_SELECTED
	global INSTANCE_NAME
	global INSTANCE_SELECTION
	global BACKFROMINSTANCES

	INSTANCE_SELECTION = ''

	while INSTANCE_SELECTION.lower() != 'q':
		if BACKFROMINSTANCES != 1:
			createEC2InstancesMENU()
		printEC2InstancesMENU()
		INSTANCE_SELECTION = input()
		try:
			value = int(INSTANCE_SELECTION)
		except ValueError:
			if INSTANCE_SELECTION.lower() == 'q':
				sys.exit(0)
			else:
				if INSTANCE_SELECTION.lower() == 'b':
					BACKFROMINSTANCES = 0
					profilesMenu()
				else:
					if INSTANCE_SELECTION.lower() == 'r':
						BACKFROMINSTANCES = 0
		else:
			if (int(INSTANCE_SELECTION) >= 0) and (int(INSTANCE_SELECTION) <= len(INSTANCE_DETAILS_ORDERED)):
				INSTANCE_NAME = INSTANCE_DETAILS_ORDERED[int(INSTANCE_SELECTION)][0]
				INSTANCE_SELECTED = INSTANCE_DETAILS_ORDERED[int(INSTANCE_SELECTION)][1]
				FindPemFile(INSTANCE_DETAILS_ORDERED[int(INSTANCE_SELECTION)][4]+'.pem')
				BACKFROMINSTANCES = 1
				EC2InstancesManageMenu()
		EC2InstancesMenu()

def profilesMenu():
	global PROFILE_SELECTED

	PROFILE_ID_SELECTED = ''

	while PROFILE_ID_SELECTED.lower() != 'q':
		printProfilesMENUHeader()
		printProfilesMENUFooter()
		PROFILE_ID_SELECTED = input()
		try:
			value = int(PROFILE_ID_SELECTED)
		except ValueError:
			if PROFILE_ID_SELECTED.lower() == 'q':
				sys.exit(0)
		else:
			if (int(PROFILE_ID_SELECTED) >= 0) and (int(PROFILE_ID_SELECTED) <= len(alias_list)):
				PROFILE_SELECTED = alias_list[int(PROFILE_ID_SELECTED)-1]
				print('Loading data from '+PROFILE_SELECTED+' ....')
				EC2InstancesMenu()
		profilesMenu()

def EC2InstancesManageMenu():

	INSTANCE_MENU_SELECT = ''
	while INSTANCE_MENU_SELECT.lower() != 'q':
		printEC2ManageInstanceMENU()
		INSTANCE_MENU_SELECT = input()
		try:
			value = int(INSTANCE_MENU_SELECT)
		except ValueError:
			if INSTANCE_MENU_SELECT.lower() == 'q':
				sys.exit(0)
			else:
				if INSTANCE_MENU_SELECT.lower() == 'b':
					break
			EC2InstancesManageMenu()
		else:
			PUBLIC_IP = getPropertyEC2Instance(INSTANCE_SELECTED, 'PublicIpAddress')
			if int(INSTANCE_MENU_SELECT) == 1:
				USERNAME = input('Username (Enter -> ubuntu)')
				if USERNAME == '':
					USERNAME = 'ubuntu'
				COMMAND = 'ssh -o StrictHostKeyChecking=no -i "'+PEM_PATH+'" '+USERNAME+'@'+PUBLIC_IP
				subprocess.call(COMMAND, shell=True)
			if int(INSTANCE_MENU_SELECT) == 2:
				USERNAME = input('Username (Enter -> ubuntu)')
				if USERNAME == '':
					USERNAME = 'ubuntu'
				SOURCE_FILES = input('Files in '+PROFILE_SELECTED+' -> '+INSTANCE_NAME+': ')
				TARGET_FILES = input('Target path: ')
				COMMAND = 'scp -o StrictHostKeyChecking=no -i "'+PEM_PATH+'" '+USERNAME+'@'+PUBLIC_IP+':'+SOURCE_FILES+' '+TARGET_FILES
				subprocess.call(COMMAND, shell=True)
			if int(INSTANCE_MENU_SELECT) == 3:
				USERNAME = input('Username (Enter -> ubuntu)')
				if USERNAME == '':
					USERNAME = 'ubuntu'
				SOURCE_FILES = input('Local Files: ')
				TARGET_FILES = input('Target path in '+PROFILE_SELECTED+' -> '+INSTANCE_NAME+': ')
				COMMAND = 'scp -o StrictHostKeyChecking=no -i "'+PEM_PATH+'" '+SOURCE_FILES+' '+USERNAME+'@'+PUBLIC_IP+':'+TARGET_FILES
				subprocess.call(COMMAND, shell=True)
			if int(INSTANCE_MENU_SELECT) == 4:
				USERNAME = input('Username (Enter -> ubuntu)')
				if USERNAME == '':
					USERNAME = 'ubuntu'
				COMMAND = input('Command : ')
				COMMAND = 'ssh -o StrictHostKeyChecking=no -i "'+PEM_PATH+'" '+USERNAME+'@'+PUBLIC_IP+' '+COMMAND
				subprocess.call(COMMAND, shell=True)
			if int(INSTANCE_MENU_SELECT) == 5:
				USERNAME = input('Username (Enter -> ubuntu)')
				if USERNAME == '':
					USERNAME = 'ubuntu'
				LOG_PATH = input('Type absolute path to log : ')
				COMMAND = 'ssh -o StrictHostKeyChecking=no  -i "'+PEM_PATH+'" '+USERNAME+'@'+PUBLIC_IP+' less '+LOG_PATH
				subprocess.call(COMMAND, shell=True)
			if int(INSTANCE_MENU_SELECT) == 6:
				USERNAME = input('Username (Enter -> ubuntu)')
				if USERNAME == '':
					USERNAME = 'ubuntu'
				GREP_FILTER = input('Write filter, empty to all : ')
				COMMAND = 'ssh -o StrictHostKeyChecking=no -i "'+PEM_PATH+'" '+USERNAME+'@'+PUBLIC_IP+' ps -fea | grep "'+GREP_FILTER+'"'
				subprocess.call(COMMAND, shell=True)
			if int(INSTANCE_MENU_SELECT) == 7:
				print('Network Tools')
			if int(INSTANCE_MENU_SELECT) == 8:
				print('Monitoring Tools')
			if int(INSTANCE_MENU_SELECT) == 9:
				EC2InstancesManageToolsMenu()

def printEC2ManageToolsInstanceMENUFooter():

	print(DASHES)
	print('1. Reboot instance')
	print('2. Stop instance')
	print('3. Start instance')
	print(DASHES)
	OPTION = 'Choose Option | '+Fore.GREEN+'r'+Fore.RESET+'efresh | '
	OPTION = OPTION +Style.BRIGHT+'b'+Style.RESET_ALL+'ack | '+Fore.RED+'q'+Fore.RESET+'uit: '
	print(OPTION)

def printEC2ManageInstanceMENUFooter():

	print(DASHES)
	print('1. Connect via SSH')
	print('2. Copy File(s) '+Style.BRIGHT+'FROM'+Style.RESET_ALL+' '+INSTANCE_NAME)
	print('3. Copy File(s) '+Style.BRIGHT+'TO'+Style.RESET_ALL+' '+INSTANCE_NAME)
	print('4. Execute command '+Style.BRIGHT+'IN'+Style.RESET_ALL+' '+INSTANCE_NAME)
	print('5. View log(s) '+Style.BRIGHT+'FROM'+Style.RESET_ALL+' '+INSTANCE_NAME)
	print('6. View Proces(s) running '+Style.BRIGHT+'IN'+Style.RESET_ALL+' '+INSTANCE_NAME)
	print('7. Network tools')
	print('8. Monitoring tools')
	print('9. Manage Tools')
	print(DASHES)
	OPTION = 'Choose Option | '+Style.BRIGHT+Fore.GREEN+'r'+Style.RESET_ALL+'efresh | '
	OPTION = OPTION +Style.BRIGHT+'b'+Style.RESET_ALL+'ack | '+Style.BRIGHT+Fore.RED
	OPTION = OPTION +'q'+Style.RESET_ALL+'uit:'
	print(OPTION)

def printEC2InstancesMENU():

	os.system('clear')
	print(DASHES)
	print('AWS EC2 INSTANCES MENU')
	print('SELECTED PROFILE : '+Style.BRIGHT+PROFILE_SELECTED+Style.RESET_ALL)
	print(DASHES)
	print(tabulate(INSTANCE_DETAILS_ORDERED, tablefmt='plain', showindex=True))
	print(DASHES)
	OPTION = 'Choose EC2 instance | '+Style.BRIGHT+Fore.GREEN+'r'+Style.RESET_ALL+'efresh | '
	OPTION = OPTION +Style.BRIGHT+'b'+Style.RESET_ALL+'ack | '+Style.BRIGHT+Fore.RED
	OPTION = OPTION +'q'+Style.RESET_ALL+'uit:'
	print(OPTION)

def printEC2ManageInstanceMENUHeader():

	os.system('clear')
	print(DASHES)
	print('AWS EC2 INSTANCES MENU')
	print('SELECTED PROFILE : '+Style.BRIGHT+PROFILE_SELECTED+Style.RESET_ALL)
	print('SELECTED INSTANCE : '+Style.BRIGHT+INSTANCE_SELECTED+' / '+INSTANCE_NAME+Style.RESET_ALL)
	print(DASHES)

def EC2InstancesManageToolsMenu():

	SELECTION = ''
	while SELECTION.lower() != 'q':
		printEC2ManageInstanceMENUHeader()
		createEC2DetailsScreen()
		printEC2ManageToolsInstanceMENUFooter()
		SELECTION = input()
		try:
			value = int(SELECTION)
		except ValueError:
			if SELECTION.lower() == 'q':
				sys.exit(0)
			else:
				if SELECTION.lower() == 'b':
					break
		else:
			if int(SELECTION) == 1:
				client.reboot_instances(InstanceIds=[INSTANCE_SELECTED], DryRun=False)
			if int(SELECTION) == 2:
				client.stop_instances(InstanceIds=[INSTANCE_SELECTED], Force=True, DryRun=False)
			if int(SELECTION) == 3:
				client.start_instances(InstanceIds=[INSTANCE_SELECTED], DryRun=False)

def createEC2DetailsScreen():

	MENU_FILE = []

	TEMP_ID = INSTANCE_DETAILS_ORDERED[int(INSTANCE_SELECTION)][1]
	TEMP_NAME = INSTANCE_DETAILS_ORDERED[int(INSTANCE_SELECTION)][0]
	TEMP_PLATFORM = INSTANCE_DETAILS_ORDERED[int(INSTANCE_SELECTION)][2]
	TEMP_STATUS = INSTANCE_DETAILS_ORDERED[int(INSTANCE_SELECTION)][3]
	TEMP_PRIVATE_IP = getPropertyEC2Instance(INSTANCE_SELECTED, 'PrivateIpAddress')
	TEMP_PRIVATE_DNS = getPropertyEC2Instance(INSTANCE_SELECTED, 'PrivateDnsName')
	TEMP_SECURITY_GROUP_ID = getPropertyEC2Instance(INSTANCE_SELECTED, 'SecurityGroups[].GroupId')
	TEMP_SECURITY_GROUP_NAME = getPropertyEC2Instance(INSTANCE_SELECTED, 'SecurityGroups[].GroupName')
	TEMP_PUBLIC_IP = getPropertyEC2Instance(INSTANCE_SELECTED, 'PublicIpAddress')
	TEMP_PUBLIC_DNS = getPropertyEC2Instance(INSTANCE_SELECTED, 'PublicDnsName')

	MENU_FILE.append(['Name: '+TEMP_NAME, 'Platform: '+TEMP_PLATFORM])
	MENU_FILE.append(['ID: '+TEMP_ID, 'Public IP: '+TEMP_PUBLIC_IP])
	MENU_FILE.append(['Private IP: '+TEMP_PRIVATE_IP, 'Public DNS: '+TEMP_PUBLIC_DNS])
	MENU_FILE.append(['Private DNS: '+TEMP_PRIVATE_DNS, 'Security Group ID: '+TEMP_SECURITY_GROUP_ID])
	MENU_FILE.append(['Status: '+TEMP_STATUS, 'Security Group Name: '+TEMP_SECURITY_GROUP_NAME])

	print(tabulate(MENU_FILE, tablefmt='plain', showindex=False))

def printEC2ManageInstanceMENU():

	printEC2ManageInstanceMENUHeader()
	createEC2DetailsScreen()
	printEC2ManageInstanceMENUFooter()

def createEC2InstancesMENU():

	global DNS
	global PLATFORM
	global STATUS
	global INSTANCETYPE
	global PUBLICIP
	global NAME
	global PEM
	global AUX_LAUNCH_TIME
	global INSTANCE_DETAILS_ORDERED

	connect_ec2()
	query = '.Reservations[].Instances[] | .InstanceId'
	INSTANCE_DETAILS_LIST = pyjq.all(query, json_data)
	INSTANCE_DETAILS = []
	i = 1
	for INSTANCE_SELECTED in INSTANCE_DETAILS_LIST:
		PLATFORM = getPropertyEC2Instance(INSTANCE_SELECTED, 'Platform')
		if PLATFORM == '-':
			PLATFORM = 'linux'
		STATUS = getPropertyEC2Instance(INSTANCE_SELECTED, 'State.Name')
		if STATUS == 'pending':
			COLORED_STATUS = Fore.YELLOW+STATUS+Style.RESET_ALL
		else:
			if (STATUS == 'stopped') or (STATUS == 'stopping') or (STATUS == 'terminated'):
				COLORED_STATUS = Fore.RED+STATUS+Style.RESET_ALL
			else:
				if STATUS == 'running':
					COLORED_STATUS = Fore.GREEN+STATUS+Style.RESET_ALL
		INSTANCETYPE = getPropertyEC2Instance(INSTANCE_SELECTED, 'InstanceType')
		PUBLICIP = getPropertyEC2Instance(INSTANCE_SELECTED, 'PublicIpAddress')
		NAME = getKeyValuePropertyEC2Instance(INSTANCE_SELECTED, 'Tags', 'Key', 'Name', 'Value')
		PEM = getPropertyEC2Instance(INSTANCE_SELECTED, 'KeyName')
		AUX_LAUNCH_TIME = getPropertyEC2Instance(INSTANCE_SELECTED, 'LaunchTime')
		if STATUS != 'running':
			UPTIME = '-'
		else:
			UPTIME = extractDeltaTime(AUX_LAUNCH_TIME)
		INSTANCE_DETAILS.append([NAME, INSTANCE_SELECTED, PLATFORM, COLORED_STATUS, PEM, INSTANCETYPE, PUBLICIP,UPTIME])
	INSTANCE_DETAILS_ORDERED = sorted(INSTANCE_DETAILS, key=lambda x: x[0])

def extractDeltaTime(AUX_LAUNCH_TIME):
	DATETIME_FORMAT = '%Y-%m-%d %H:%M:%S+00:00'
	UPTIME = datetime.now() - datetime.strptime(AUX_LAUNCH_TIME, DATETIME_FORMAT)
	days, seconds = UPTIME.days, UPTIME.seconds
	hours = seconds // 3600
	minutes = (seconds % 3600) // 60
	seconds = (seconds % 60)
	return '{:=03d}'.format(UPTIME.days)+'d '+'{:=02d}'.format(hours)+'h ' +'{:=02d}'.format(minutes)+'m ' +'{:=02d}'.format(seconds)+'s'

def getPropertyEC2Instance(INSTANCE_SELECTED, PROPERTY_SEARCHED):

	query = '.Reservations[].Instances[] | select (.InstanceId == \"'
	query = query +str(INSTANCE_SELECTED)+'\") | .'+str(PROPERTY_SEARCHED)
	list = pyjq.all(query, json_data)
	if list[0] is None:
		return '-'
	else:
		if (str(PROPERTY_SEARCHED) == 'SecurityGroups[].GroupName') or ((str(PROPERTY_SEARCHED) == 'SecurityGroups[].GroupId')):
			STRING_2_RETURN = ''
			for i in range(len(list)):
				STRING_2_RETURN = STRING_2_RETURN + list[i] + ' '
			return STRING_2_RETURN
		else:
			return list[0]

def main():
	check_file_expiration_dates()
	if PROFILE_EXPIRED == 1:
		username_password_login()
		check_if_mfa()
		mfa_login()
		check_saml_mfa()
		retrive_roles()
		order_roles()
		write_config_file()
	profilesMenu()

if __name__ == "__main__":
	main()
