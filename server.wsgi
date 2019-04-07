#! /user/bin/python3.7 
import logging
import sys
logging.basicConfig(stream=sys.stderr)
sys.path.insert(0,'/var/www/html/scout/')

activate_this = '/var/www/html/scout/scout/bin/activate_this.py'
with open(activate_this) as file_:
    exec(file_.read(), dict(__file__=activate_this))

from server import app as application
application.root_path = '/var/www/html/scout/'
application.secret_key='scout'
