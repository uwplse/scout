# Start up the Spectrum project at http://localhost:5000
ttab -a Terminal "source scout/bin/activate; ./run_continuously.sh"
ttab -a Terminal "cd static; npm run watch"
ttab -a Terminal "tail -f server.out"


