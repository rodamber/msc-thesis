FROM python:3.7.5-buster AS dev
WORKDIR /app
COPY . .
RUN pip install -r requirements.txt
WORKDIR /app/z3
RUN python scripts/mk_make.py --python
WORKDIR /app/z3/build
RUN make && make install
CMD ["/bin/bash"]

FROM dev AS app
WORKDIR /app
ENTRYPOINT ["python", "src/runsynth.py"]
