FROM golang
ADD crypto.go /go
RUN cd /go && \
    go build crypto.go && \
    rm crypto.go
EXPOSE 1812 
CMD ["/go/crypto"]
