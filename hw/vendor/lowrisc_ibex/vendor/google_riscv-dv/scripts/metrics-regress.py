#!/usr/bin/python3

import json
import http.client
import argparse
import os
import time
import math

def make_http_request( req_type, endpoint, params=None ):
    headers = { 'Content-Type': 'application/json',
                'Private-Token': str(os.environ['METRICS_CI_TOKEN'])
               }
    
    conn = http.client.HTTPSConnection(server)
    conn.request(req_type, endpoint, params, headers)
    response = conn.getresponse()
    data = response.read()
    regressionData = json.loads(data.decode('utf-8'))
    conn.close()

    return response, regressionData


## Parse arguments to get regression name and project ID
parser = argparse.ArgumentParser(prog='metrics-regress',
                                 description='Launch a regression on the Metrics platform and query results')
parser.add_argument('regressionName', help='The name of the regression to run')
parser.add_argument('projectId',      help='The ID of the Metrics project')
args = parser.parse_args()

## Server
server =  'chipsalliance.metrics.ca:443'

## API Endpoints
postRegression = '/api/v1/projects/'+args.projectId+'/regressionRuns'
getRegressionRunInfo = '/api/v1/projects/'+args.projectId+'/regressionRuns/'

## Start regression
reqParams = {}
reqParams['regressionName'] = args.regressionName

# Determine the git reference to pass to Metrics. For PRs, the reference
# is of the format refs/pull/<PR-number>/merge
if str(os.environ['GITHUB_EVENT_NAME']) == 'pull_request_target':
    reqParams['branch'] = 'refs/pull/' + str(os.environ['PR_NUMBER']) + '/merge'
else:
    reqParams['branch'] = str(os.environ['GITHUB_REF'])
params = json.dumps(reqParams)

response, regressionData = make_http_request('POST', postRegression, params) 

## Check response
if response.status != 201:
    print('Error, regression was not started. Response: ' + str(response.status) + ':' \
          + str(response.reason) + ' ' + str(regressionData))
    print('Exit with code 1')
    exit(1)
else:
    print('Regression started. Id = ' + regressionData['id'])

## Start polling regression status
regressionRunId = regressionData['id']

while True:
    time.sleep(10)
    response, regressionData = make_http_request('GET', getRegressionRunInfo+regressionRunId)
    if response.status == 200:
        if 'complete' in regressionData['status']:
            print('Regression complete')
            break
        if 'buildFailed' in regressionData['status']:
            print('A build has failed. No tests will be run')
            print('Debug at: https://chipsalliance.metrics.ca/' + args.projectId + \
                  '/results/regressionRuns/' + regressionRunId)
            exit(1)

## Print test status
print('\n')
print('Regression results')
print('==================')
print('Total number of tests: ' + str(regressionData['testRuns']['total']))
print('Passed tests: ' + str(regressionData['testRuns']['passed']))
print('Failed tests: ' + str(regressionData['testRuns']['failed']))
print('Incomplete tests: ' + str(regressionData['testRuns']['incomplete']))
print('\n')

## Poll for coverage data
#while True:
#    time.sleep(10)
#    response, regressionData = make_http_request('GET', getRegressionRunInfo+regressionRunId)
#    if response.status is 200:
#        if regressionData['functionalCoverage'] is not None :
#            break

## Print functional coverage
#print('Coverage results')
#print('================')
#print('Functional: ' + str(math.trunc(regressionData['functionalCoverage']*100)/100))
#if regressionData['assertionCoverage'] is not None:
#    print('Assertion: ' + str(math.trunc(regressionData['assertionCoverage']*100) /100))
#if regressionData['lineCoverage'] is not None:
#    print('Code (block): ' + str(math.trunc(regressionData['lineCoverage']*100) /100))
#print('\n')

print('Full results at: https://chipsalliance.metrics.ca/' + args.projectId + \
      '/results/regressionRuns/' + regressionRunId)
      
## Set the exit code to be used by github action
if regressionData['testRuns']['failed'] > 0 or \
   regressionData['testRuns']['incomplete'] > 0:
    print('One or more tests has failed/is incomplete. Exit with code 1.')
    exit(1)
else:
    print('All tests have passed. Exit with code 0.')
    exit(0)

    
                                                 

                                                 
                        
