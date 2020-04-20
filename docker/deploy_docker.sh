#!/bin/sh
heroku login
heroku create
heroku container:push web
heroku container:release web
