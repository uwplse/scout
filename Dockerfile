FROM python:3.5

RUN apt-get update -qq && apt-get install -yqq curl
RUN curl -sL https://deb.nodesource.com/setup_9.x | bash
RUN apt-get install -yqq nodejs
RUN apt-get clean -y

COPY ./requirements.txt /scout/requirements.txt
WORKDIR /scout

RUN pip install -r requirements.txt
COPY . /scout

RUN git clone https://github.com/Z3Prover/z3
RUN cd /scout/z3/ && python scripts/mk_make.py --python
RUN cd /scout/z3/build && make && make install 

RUN cd /scout/static/ && npm install

# EXPOSE 5000
ENTRYPOINT ["python"]
CMD [ "server.py"]
