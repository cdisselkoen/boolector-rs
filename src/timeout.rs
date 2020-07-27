use std::sync::RwLock;
use std::time::{Duration, Instant};

#[derive(Debug)]
pub struct TimeoutState {
    timeout_duration: RwLock<Option<Duration>>,
    current_operation_start_time: RwLock<Instant>,
}

impl TimeoutState {
    pub fn new() -> Self {
        Self::with_timeout_duration(None)
    }

    pub fn with_timeout_duration(timeout_duration: Option<Duration>) -> Self {
        Self {
            timeout_duration: RwLock::new(timeout_duration),
            current_operation_start_time: RwLock::new(Instant::now()),
        }
    }

    pub fn get_timeout_duration(&self) -> Option<Duration> {
        let guard = self.timeout_duration.read().unwrap();
        *guard
    }

    pub fn set_timeout_duration(&self, timeout_duration: Option<Duration>) {
        let mut guard = self.timeout_duration.write().unwrap();
        *guard = timeout_duration;
    }

    pub fn get_current_operation_start_time(&self) -> Instant {
        let guard = self.current_operation_start_time.read().unwrap();
        *guard
    }

    pub fn restart_timer(&self) {
        let mut guard = self.current_operation_start_time.write().unwrap();
        *guard = Instant::now();
    }
}

pub extern "C" fn callback(void_ptr_to_ts: *mut std::os::raw::c_void) -> i32 {
    let timeout_state = unsafe { &*(void_ptr_to_ts as *const TimeoutState) };
    match timeout_state.get_timeout_duration() {
        None => 0, // no timeout set, keep going
        Some(timeout_duration) => {
            let current_operation_start_time = timeout_state.get_current_operation_start_time();
            match Instant::now().checked_duration_since(current_operation_start_time) {
                None => {
                    // somehow negative time has elapsed since operation started?  Keep going
                    0
                },
                Some(duration) => {
                    if duration > timeout_duration {
                        1 // terminate
                    } else {
                        0 // keep going
                    }
                },
            }
        },
    }
}
