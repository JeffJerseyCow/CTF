import os
import sys
import json
from flask_mail import Mail, Message
from flask import Flask, url_for, render_template, request, redirect

# load email secrets
mail_username = os.getenv('MAIL_USERNAME')
mail_password = os.getenv('MAIL_PASSWORD')
if mail_username == None or mail_password == None:
    print('Cannot load email configuration')
    sys.exit(False)

# get contact emails
emails = os.getenv('EMAILS')
if emails == None:
    print('Cannot load emails')
    sys.exit(False)
emails = json.loads(emails)

# get flags
flags = {'crypto_flag': os.getenv('CRYPTO_FLAG'),
         'solver_flag': os.getenv('SOLVER_FLAG'),
         'revenge_flag': os.getenv('REVENGE_FLAG')}
for k, v in flags.items():
    if v == None:
        print('Cannot find %s' % k)
        sys.exit(False)

# get server addresses
addrs = {'crypto_addr': os.getenv('CRYPTO_ADDR'),
         'solver_addr': os.getenv('SOLVER_ADDR'),
         'revenge_addr': os.getenv('REVENGE_ADDR')}
for k, v in addrs.items():
    if v == None:
        print('Cannot find %s' % k)
        sys.exit(False)

# configuration
app = Flask(__name__)
app.config.update(dict(
    DEBUG = True,
    MAIL_SERVER = 'smtp.gmail.com',
    MAIL_PORT = 587,
    MAIL_USE_TLS = True,
    MAIL_USE_SSL = False,
    MAIL_USERNAME = mail_username,
    MAIL_PASSWORD = mail_password,
))
mail = Mail(app)

# index
@app.route('/')
def index():
    return render_template('index.html',
                           crypto_addr=addrs['crypto_addr'],
                           solver_addr=addrs['solver_addr'],
                           revenge_addr=addrs['revenge_addr'])

# check flag
@app.route('/flag', methods=['GET', 'POST'])
def check_flag():
    if request.method == 'POST':
        name = request.form.get('name')
        email = request.form.get('email')
        flag = request.form.get('flag')
        if len(name) == 0 or len(email) == 0:
            return render_template('error.html',
                                   error='Missing name or email')
        for k, v in flags.items():
            if flag == v:
                msg = Message("Cyber Challenge Winner",
                              sender="cyberform", recipients=emails)
                msg.body = "Name: %s\nEmail: %s\nFlag: %s" % (name, email, k)
                mail.send(msg)
                return render_template('congrats.html', name=name,
                                       flag_name=k)
    else:
        return redirect(url_for('index'))

    # default
    return render_template('unlucky.html')
