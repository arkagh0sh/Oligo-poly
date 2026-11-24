//! The desktop program: serves the web page on this computer and opens it in
//! the default browser. The computations run natively, each in a child process
//! of the program, so that the Stop button can end them at once.
//!
//! Usage: `equivariant-groebner [--no-browser] [--port N]`.
//! The program runs until it is closed (for example with Ctrl+C).

use std::collections::hash_map::RandomState;
use std::hash::BuildHasher;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

/// The page, without the WebAssembly module: it then sends its requests to
/// this program.
const PAGE : &str = include_str!("../page.html");

/// The largest request that the server reads, in bytes.
const MAX_BODY : usize = 1 << 20;

struct Server {
    /// The secret part of the address of the page. Every request must carry
    /// it, so that other web pages cannot use the server.
    token : String,
    /// The values of the header `Host` that are accepted.
    hosts : Vec<String>,
    /// The child process of the running computation, if any.
    computation : Mutex<Option<Child>>,
}

fn main() {
    let args : Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("--compute") {
        compute_from_stdin();
        return;
    }
    let open = !args.iter().any(|a| a == "--no-browser");
    let port : u16 = args
        .iter()
        .position(|a| a == "--port")
        .and_then(|i| args.get(i + 1))
        .and_then(|p| p.parse().ok())
        .unwrap_or(0);
    let listener = match TcpListener::bind(("127.0.0.1", port)) {
        Ok(listener) => listener,
        Err(e) => {
            eprintln!("cannot listen on 127.0.0.1:{port}: {e}");
            std::process::exit(1);
        }
    };
    let port = listener.local_addr().map(|a| a.port()).unwrap_or(port);
    let server = Arc::new(Server {
        token : new_token(),
        hosts : vec![format!("127.0.0.1:{port}"), format!("localhost:{port}")],
        computation : Mutex::new(None),
    });
    let url = format!("http://127.0.0.1:{port}/?t={}", server.token);
    println!("Equivariant Gröbner bases: the page is at");
    println!("  {url}");
    println!("Keep this window open while you use the page; close it (or press Ctrl+C) to quit.");
    if open {
        open_browser(&url);
    }
    for stream in listener.incoming().flatten() {
        let server = Arc::clone(&server);
        std::thread::spawn(move || {
            let _ = handle(stream, &server);
        });
    }
}

/// The child process: reads a request on its standard input and writes the
/// answer on its standard output.
fn compute_from_stdin() {
    let mut request = String::new();
    if std::io::stdin().read_to_string(&mut request).is_err() {
        return;
    }
    let answer = oligo_poly_web::run(&request);
    print!("{}", serde_json::to_string(&answer).unwrap_or_default());
}

/// A random token of 32 hexadecimal digits.
fn new_token() -> String {
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    let a = RandomState::new().hash_one(nanos);
    let b = RandomState::new().hash_one((nanos, a));
    format!("{a:016x}{b:016x}")
}

fn open_browser(url : &str) {
    let result = if cfg!(target_os = "macos") {
        Command::new("open").arg(url).spawn()
    } else if cfg!(target_os = "windows") {
        Command::new("cmd").args(["/C", "start", "", url]).spawn()
    } else {
        Command::new("xdg-open").arg(url).stdout(Stdio::null()).stderr(Stdio::null()).spawn()
    };
    if result.is_err() {
        println!("Open the address above in your browser.");
    }
}

/// A request: the method, the path, the query, the header `Host`, and the body.
struct Request {
    method : String,
    path : String,
    query : String,
    host : String,
    body : Vec<u8>,
}

fn read_request(stream : &TcpStream) -> std::io::Result<Request> {
    let mut reader = BufReader::new(stream);
    let mut line = String::new();
    reader.read_line(&mut line)?;
    let mut words = line.split_whitespace();
    let method = words.next().unwrap_or("").to_string();
    let target = words.next().unwrap_or("/");
    let (path, query) = target.split_once('?').unwrap_or((target, ""));
    let (path, query) = (path.to_string(), query.to_string());
    let mut host = String::new();
    let mut length = 0;
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 || line.trim().is_empty() {
            break;
        }
        if let Some((name, value)) = line.split_once(':') {
            match name.trim().to_ascii_lowercase().as_str() {
                "host" => host = value.trim().to_string(),
                "content-length" => length = value.trim().parse().unwrap_or(0),
                _ => {}
            }
        }
    }
    let mut body = vec![0; length.min(MAX_BODY)];
    reader.read_exact(&mut body)?;
    Ok(Request { method, path, query, host, body })
}

fn respond(mut stream : &TcpStream, status : &str, content_type : &str, body : &[u8]) -> std::io::Result<()> {
    write!(
        stream,
        "HTTP/1.1 {status}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n",
        body.len()
    )?;
    stream.write_all(body)?;
    stream.flush()
}

fn handle(stream : TcpStream, server : &Server) -> std::io::Result<()> {
    let request = read_request(&stream)?;
    let authorised = server.hosts.contains(&request.host) && request.query == format!("t={}", server.token);
    if !authorised {
        return respond(&stream, "403 Forbidden", "text/plain; charset=utf-8", b"forbidden");
    }
    match (request.method.as_str(), request.path.as_str()) {
        ("GET", "/") => {
            let page = PAGE.replace("__WASM_BASE64__", "");
            respond(&stream, "200 OK", "text/html; charset=utf-8", page.as_bytes())
        }
        ("POST", "/compute") => {
            let answer = run_child(server, &request.body);
            respond(&stream, "200 OK", "application/json", answer.as_bytes())
        }
        ("POST", "/stop") => {
            if let Some(child) = server.computation.lock().unwrap().as_mut() {
                let _ = child.kill();
            }
            respond(&stream, "200 OK", "application/json", b"{}")
        }
        _ => respond(&stream, "404 Not Found", "text/plain; charset=utf-8", b"not found"),
    }
}

/// Runs a request in a child process, and returns its answer. A new request
/// stops the previous one.
fn run_child(server : &Server, request : &[u8]) -> String {
    let internal = |message : String| serde_json::json!({ "status" : "internal-error", "message" : message }).to_string();
    let program = match std::env::current_exe() {
        Ok(program) => program,
        Err(e) => return internal(format!("cannot find the program: {e}")),
    };
    let spawned = Command::new(program)
        .arg("--compute")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();
    let mut child = match spawned {
        Ok(child) => child,
        Err(e) => return internal(format!("cannot start the computation: {e}")),
    };
    let id = child.id();
    let (mut stdout, mut stderr) = (child.stdout.take().unwrap(), child.stderr.take().unwrap());
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(request);
    }
    if let Some(mut previous) = server.computation.lock().unwrap().replace(child) {
        let _ = previous.kill();
        let _ = previous.wait();
    }
    let errors = std::thread::spawn(move || {
        let mut text = String::new();
        let _ = stderr.read_to_string(&mut text);
        text
    });
    let mut answer = String::new();
    let _ = stdout.read_to_string(&mut answer);
    let errors = errors.join().unwrap_or_default();
    // The child is still registered unless a newer request replaced it, which
    // then also stopped and waited for it.
    let finished = {
        let mut computation = server.computation.lock().unwrap();
        if computation.as_ref().map(Child::id) == Some(id) {
            computation.take().and_then(|mut child| child.wait().ok())
        } else {
            None
        }
    };
    match finished {
        Some(status) if status.success() && !answer.is_empty() => answer,
        Some(status) if !status.success() && !errors.trim().is_empty() => internal(errors.trim().to_string()),
        _ => serde_json::json!({ "status" : "stopped" }).to_string(),
    }
}
